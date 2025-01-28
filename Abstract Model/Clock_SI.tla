---- MODULE Clock_SI ----
EXTENDS TLC,FiniteSets,Sequences,Integers,Util
CONSTANTS KEY,       \* Set of all keys
          VALUES,    \* Set of all values
          NOVAL,     \* the value null 
          PART,      \* Ids of partitons
          TX_ID,     \* transactions ID's
          TIME_DIST ,\* Max update to time 
          KEY_PART,  \* Function that maps a key to a partition
          PART_KEY,  \* Function that maps a partition to a key
          MAX_TIME   \* Max time value

ASSUME \A key \in (DOMAIN KEY_PART): key \in PART_KEY[KEY_PART[key]] 
ASSUME \A part \in PART: PART_KEY[part] # {}

ASSUME TIME_DIST > 0
ASSUME MAX_TIME > 0

VARIABLES 
\* Partition variables 
          db,             \* Function that represents Key-value database
          tx_status,      \* Function that maps a transaction to his status 
          partition_time, \* Simulation of real time 
\* Snapshot variables 

          read_keys,      \* Function that maps a transaction to a set of keys to read 
          write_keys,     \* Function that maps a transaction to a set of keys to write 
\* Client-centric variables
          ops

vars      == <<db,tx_status,partition_time,read_keys,write_keys,ops>>
vars_snap == <<read_keys,write_keys,partition_time>>

CC == INSTANCE ClientCentric WITH Keys <- KEY, Values <-  VALUES         
    
\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)
InitialState == [k \in KEY |-> NOVAL]

START_TIMESTAMP == 1

tx_status_view ==
    LET
        time(tx) == IF tx_status[tx].commit_timestamp # NOVAL /\ tx_status[tx].write_set = {}
                    THEN tx_status[tx].commit_timestamp
                    ELSE tx_status[tx].start_timestamp
    IN
        [tx \in TX_ID |-> [status |-> tx_status[tx].status,
                           time |-> time(tx),
                           read_set |-> tx_status[tx].read_set,
                           write_set |-> tx_status[tx].write_set,
                           commit_set |-> tx_status[tx].commit_set]]

partition_time_view ==
    LET
        min_p == CHOOSE x \in PART:(\A p \in PART: partition_time[x] <= partition_time[p])
    IN
        [p \in PART |-> partition_time[p] - partition_time[min_p]]

vars_view == <<db,tx_status,partition_time,read_keys,write_keys>>

\* Data types --------------------------------------------------------

TIME == 0..100\*Nat

TIMESTAMP == [PART -> TIME]

\* Possible states for a database entry
STATE_ENTRY == {"COMMITTED","PREPARED","ABORTED"}

\* Defenition of a database entry
DB_ENTRY == [
    \* val -> value associated to the key
    val:VALUES \union {NOVAL},
    \* state -> state of the entry
    state:STATE_ENTRY,
    \* timestamp -> is only defined when state changes to "COMMITTED"
    timestamp:TIME,
    \* tx -> transaction id responsible by the write
    tx:TX_ID \union {NOVAL}]

\* Possible states for a coordinator

TRANSACTION_STATUS == {"RUNNING","ABORTING"}


\* State needed by a transaction
TRANSACTION_ENTRY == [
    \* status -> stores the current status of the transaction 
    status: TRANSACTION_STATUS,
    \* read_set -> set of keys that a transaction needs to read
    read_set:SUBSET KEY,
    \* write_set -> set of keys that a transaction needs to write 
    write_set:SUBSET KEY,
    \* commit_set -> set of keys that a transaction needs commit 
    \* if state = "ABORTING" is the set of key it needs to turn from "PREPARED" to ABORTED 
    commit_set:SUBSET KEY,
    \* start_timestamp -> start timestamp of a transaction
    start_timestamp:TIME \union {NOVAL},
    \* commit_timestamp -> commit timestamp of a transaction
    commit_timestamp: TIME \union {NOVAL}]

\* Expantion upon the operation type defined in the Client-centric 
\* Add field time 
Operation == [op: {"read", "write"}, key: KEY, value: VALUES, time: TIME \union {NOVAL}]

\* Auxiliar functions --------------------------------------------

\* Tranforms a set to a unique sequence 
SetToSeq(s) == CHOOSE f \in [1..Cardinality(s) -> s] : IsInjective(f) 

Abs(n) == IF n < 0 THEN -n ELSE n

Max(x,y) == IF x > y THEN x ELSE y

Finished == (\A tx \in TX_ID: 
                /\ tx_status[tx].read_set = {} 
                /\ tx_status[tx].write_set = {} 
                /\ tx_status[tx].commit_set = {})

\* Retrive the current time of a partition
Get_time(p) == partition_time[p] 

Update_time == \E p \in PART: 
                    LET 
                        new_time == [partition_time EXCEPT ![p] = partition_time[p] + 1]
                    IN
                        /\ \A p1 \in PART:Abs(new_time[p] - new_time[p1]) <= TIME_DIST
                        /\ partition_time' = new_time
                        /\ UNCHANGED <<db,tx_status,read_keys,write_keys,ops>>

Get_start_timestamp(tx,p) == IF tx_status[tx].start_timestamp = NOVAL 
                             THEN Get_time(p)
                             ELSE tx_status[tx].start_timestamp

\* Given a transaction tx and a set of keys it retrives
\* it retrives a set of partition that have the clock greater
\* or equal to the transaction's start_timestamp and are responsible 
\* for that key
Accessible_partitions(tx,set) == 
    LET
        partitions_set == {KEY_PART[k]:k \in set}
    IN
        IF tx_status[tx].start_timestamp = NOVAL
        THEN partitions_set
        ELSE {p \in partitions_set: tx_status[tx].start_timestamp <= Get_time(p)}

\* Given a transaction tx and a set of keys it retrives
\* it retrives a set of keys that are save in a partition that has the clock greater
\* or equal to the transaction's start_timestamp
Accessible_keys(tx,set) == 
    {key \in set: KEY_PART[key] \in Accessible_partitions(tx,set)}

\* Checks if there isn't a write-write conflict 
\* If a there is a version of this key commited then it must have been commited after th start timestamp
\* It can be no prepared version for this key 
Check_key_write(start_timestamp,tx,key) == 
    \A version \in (DOMAIN db[key]):
        /\ (db[key][version].state = "COMMITTED" => db[key][version].timestamp < start_timestamp)
        /\ (db[key][version].state # "PREPARED")

\* Checks if there is a write-write conflict for a transaction to abort
\* it must exist a version "COMMITTED" with a higher commit timestamp
Check_key_abort(start_timestamp,tx,key) ==
    \E version \in (DOMAIN db[key]): 
        /\ (db[key][version].state = "COMMITTED" /\ db[key][version].timestamp > start_timestamp)

\* Checks if the entry choosen is a valid entry to be read
\* Starts by ensuring the transaction start_timesamp is greater then the entry commit timesamp
\* Then ensures there isn t any entry for this key in the prepared state
\* Then ensures that this entry is the entry with the greatest timesamp of all avilable entrys
Check_key_read(start_timestamp,key,entry) == 
    /\ start_timestamp > entry.timestamp 
    /\ entry.state = "COMMITTED" 
    /\ \A version \in (DOMAIN db[key]):
        /\ db[key][version].state # "PREPARED"
        /\ (entry # db[key][version] /\ 
            db[key][version].timestamp < start_timestamp /\ 
            db[key][version].state # "ABORTED") => db[key][version].timestamp < entry.timestamp

\*  -----------------------------------------------------------------------------------
\* Auxiliar predicates to change the variable ops 

\* Adds entrys from read operations 
Read_ops(tx,key,val) == 
    LET entry == [op |-> "read", key |-> key, value |-> val, time |-> NOVAL]
    IN ops' = [ops EXCEPT ![tx] = Append(ops[tx], entry)]

\* Adds entrys from write operations 
Write_ops(tx,fun) == 
    LET set_entry == {[op |-> "write",key |-> k, value |-> tx, time |-> fun[k]]:k \in (DOMAIN fun)}
    IN ops' = [ops EXCEPT ![tx] = ops[tx] \o SetToSeq(set_entry)]  

\* In case of abort remove all write operations added
Clean_ops(tx) == ops' = [ops EXCEPT ![tx] = SelectSeq(ops[tx],LAMBDA x: x.op = "read")]

\* Retrive a set of times for every write
Get_time_ops(tx) == LET
                        aux == SelectSeq(ops[tx],LAMBDA n:n.op = "write")
                    IN
                        {aux[n].time:n \in (DOMAIN aux)}

\* Retrive a set of key already writed
Get_writed_keys_ops(tx) == LET
                                aux == SelectSeq(ops[tx],LAMBDA n:n.op = "write")
                           IN {n \in (DOMAIN aux):aux[n].key}

\*---------------------------------------------------- 

Read(tx) ==
    /\ tx_status[tx].status = "RUNNING"
    /\ tx_status[tx].read_set # {}
    /\ \E key \in tx_status[tx].read_set:
        LET 
            p == KEY_PART[key]
            start_timestamp == Get_start_timestamp(tx,p)
            new_read_set == tx_status[tx].read_set \ {key}

        IN
            \* Eunsures that the start timestamp isn't in the future
            /\ start_timestamp <= Get_time(p) 
            /\ \E n \in (DOMAIN db[key]):
                 /\ Check_key_read(start_timestamp,key,db[key][n])
                 /\ tx_status' = [tx_status EXCEPT ![tx] = [
                                    read_set |-> new_read_set,
                                    start_timestamp |-> start_timestamp] @@ tx_status[tx]]
                 /\ Read_ops(tx,key,db[key][n].val)
            /\ UNCHANGED <<db>>

Write(tx) == 
    /\ tx_status[tx].status = "RUNNING"
    /\ tx_status[tx].read_set = {}
    /\ tx_status[tx].write_set # {}
    /\ \E p \in {KEY_PART[k]:k \in tx_status[tx].write_set}:
        LET
            start_timestamp == Get_start_timestamp(tx,p)
            keys == PART_KEY[p] \intersect tx_status[tx].write_set 
            prepared_timestamp == Get_time(p)
            write_times == [key \in keys |-> prepared_timestamp]

            timestamps_previous_writes == Get_time_ops(tx) \union {prepared_timestamp}
            commit_timestamp == IF tx_status[tx].commit_timestamp = NOVAL
                                THEN prepared_timestamp
                                ELSE Max(tx_status[tx].commit_timestamp, prepared_timestamp)
            new_write_set == tx_status[tx].write_set \ keys 
            new_entry == [val|->tx,timestamp|->prepared_timestamp,state|->"PREPARED",tx|->tx]

          IN
             \* Ensures that the start timestamp isn't in the future
             /\ start_timestamp <= Get_time(p) 
             /\ \A key \in keys: Check_key_write(start_timestamp,tx,key)
             /\ tx_status' = [tx_status EXCEPT ![tx] = 
                                [write_set |-> new_write_set,
                                 start_timestamp |-> start_timestamp,
                                 commit_timestamp |-> commit_timestamp] @@ tx_status[tx]]
             /\ Write_ops(tx,write_times)
             /\ db' = [key \in keys |-> Append(db[key],new_entry)] @@ db 



Abort_write(tx) ==
    /\ tx_status[tx].status = "RUNNING"
    /\ tx_status[tx].read_set = {}
    /\ tx_status[tx].write_set # {}
    /\ \E p \in {KEY_PART[k]:k \in tx_status[tx].write_set}:
        LET
            start_timestamp == Get_start_timestamp(tx,p)
            keys == PART_KEY[p] \intersect tx_status[tx].write_set 
            keys_to_abort == write_keys[tx] \ keys
            abort_time == Get_time(p)
            abort_entry == [val|->tx,timestamp|->abort_time,state|->"ABORTED",tx |-> tx]

        IN 
            /\ start_timestamp <= Get_time(p) 
            /\ \E key \in keys: Check_key_abort(start_timestamp,tx,key)
            /\ db' = [key \in keys |-> Append(db[key],abort_entry)] @@ db
            /\ Clean_ops(tx)
            /\ tx_status' = [tx_status EXCEPT ![tx] = 
                                [status|-> "ABORTING",
                                 start_timestamp |-> start_timestamp,
                                 commit_timestamp |-> abort_time,
                                 write_set |-> {},
                                 commit_set |-> keys_to_abort] @@ tx_status[tx]]


Commit(tx) ==
    /\ tx_status[tx].status = "RUNNING"
    /\ tx_status[tx].read_set = {}
    /\ tx_status[tx].write_set = {}
    /\ tx_status[tx].commit_set # {}
    /\ \E p \in {KEY_PART[k]:k \in tx_status[tx].commit_set}:
        LET
            keys == PART_KEY[p] \intersect tx_status[tx].commit_set
            commit_timestamp == tx_status[tx].commit_timestamp

            update_entry(entry) == 
                IF entry.state = "PREPARED" /\ entry.tx = tx 
                THEN [state |-> "COMMITTED",timestamp |-> commit_timestamp] @@ entry 
                ELSE entry

            aux_db == [key \in keys |-> [n \in (DOMAIN db[key]) |-> update_entry(db[key][n])]]
            new_db == aux_db @@ db

            new_commit_set == tx_status[tx].commit_set \ keys
        IN
            /\ db' = new_db
            /\ tx_status' = [tx_status EXCEPT ![tx] = [commit_set |-> new_commit_set] @@ tx_status[tx]]
            /\ UNCHANGED <<ops>>


Abort(tx) ==
    /\ tx_status[tx].status = "ABORTING"
    /\ tx_status[tx].commit_set # {}
    /\ \E p \in {KEY_PART[k]:k \in tx_status[tx].commit_set}:
        LET
            abort_time == tx_status[tx].commit_timestamp
            keys == PART_KEY[p] \intersect tx_status[tx].commit_set
            preped_keys == {key \in keys: \E n \in (DOMAIN db[key]): 
                                /\ db[key][n].state = "PREPARED" 
                                /\ db[key][n].tx = tx}
            
            update_entry(entry) == IF entry.state = "PREPARED" 
                                   THEN [state |-> "ABORTED",timestamp |-> abort_time] @@ entry 
                                   ELSE entry

            abort_entry == [val|->tx,timestamp|-> abort_time,state|->"ABORTED",tx |-> tx]
            preped_db == [key \in preped_keys |-> [n \in (DOMAIN db[key]) |-> update_entry(db[key][n])]]
            orthers_db == [key \in (keys \ preped_keys) |-> Append(db[key],abort_entry)]
            new_db == (preped_db @@ orthers_db) @@ db

            new_commit_set == tx_status[tx].commit_set \ keys
        IN
            /\ db' = new_db
            /\ tx_status' = [tx_status EXCEPT ![tx] = [commit_set |-> new_commit_set] @@ tx_status[tx]]
            /\ UNCHANGED <<ops>>

\*------------------------------------------------------------------------

Next_action == /\ UNCHANGED vars_snap 
               /\ \E tx \in TX_ID:
                 ((   Abort(tx)
                   \/ Commit(tx) 
                   \/ Abort_write(tx)
                   \/ Write(tx)
                   \/ Read(tx)))  
            
End_stutter == Finished /\ UNCHANGED vars

\*---------------------------------------------------------------------------------

Init == 
        /\ read_keys \in [TX_ID -> SUBSET KEY]
        /\ write_keys \in [TX_ID -> SUBSET KEY]
        /\ \A tx \in TX_ID: (read_keys[tx] \union write_keys[tx]) # {}
        /\ db = [k \in KEY |-> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |->NOVAL]>>] 
        /\ tx_status = [tx \in TX_ID |-> [status |-> "RUNNING",
                                          start_timestamp |-> NOVAL,
                                          commit_timestamp |-> NOVAL,
                                          read_set |-> read_keys[tx],
                                          write_set |-> write_keys[tx],
                                          commit_set |-> write_keys[tx]]]
        /\ partition_time = [p \in PART |-> START_TIMESTAMP]
        /\ ops = [tx \in TX_ID |-> <<>>] 

Next == (~Finished /\ (Next_action \/ Update_time)) \/ End_stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) 

\*PROPERTYS ---------------------------------------------------------------------- 

Type_OK == /\ write_keys \in [TX_ID -> SUBSET KEY]
           /\ read_keys \in [TX_ID -> SUBSET KEY]
           /\ partition_time \in TIMESTAMP
           /\ tx_status \in [TX_ID -> TRANSACTION_ENTRY]
           /\ PART_KEY \in [PART -> SUBSET KEY]
           /\ KEY_PART \in [KEY -> PART]
           /\ db \in [KEY -> Seq(DB_ENTRY)]
           /\ ops \in [TX_ID -> Seq(Operation)] 

Inv_create_entry == [][\A key \in KEY:\A entry \in ((DOMAIN db'[key])\(DOMAIN db[key])): db'[key][entry].state \in {"PREPARED","ABORTED"}]_vars

Create_entry == [](db = [k \in KEY |-> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |->NOVAL]>>])

Update_commit_entry == [][\A key \in KEY: \A entry \in DOMAIN db[key]: (db[key][entry].state = "PREPARED") => (db'[key][entry].state \in {"PREPARED","ABORTED"})]_vars

Update_abort_entry == [][\A key \in KEY: \A entry \in DOMAIN db[key]: (db[key][entry].state = "PREPARED") => (db'[key][entry].state \in {"PREPARED","COMMITTED"})]_vars

SnapshotIsolation == (Finished) => CC!SnapshotIsolation(InitialState, Range(ops))

Serializability == (Finished) => CC!Serializability(InitialState, Range(ops))

\* Ensures that eventually all transactions end 
All_finish == <> Finished

Deadlock_state == /\ (\A key \in KEY: \E entry \in DOMAIN db[key]: db[key][entry].state = "PREPARED") 
                  /\ (\A tx \in TX_ID: Cardinality(write_keys[tx]) = 2 /\ Cardinality(tx_status[tx].write_set) = 1)

Test_deadlock ==  [][Deadlock_state => \A key \in KEY: \E entry \in DOMAIN db'[key]: db'[key][entry].state = "PREPARED"]_vars

Evolution_correct(tx) == tx_status[tx].status = "RUNNING" /\ (
    \/ tx_status[tx].read_set # {} => Cardinality(tx_status'[tx].read_set) <=Cardinality(tx_status[tx].read_set) 
    \/ tx_status[tx].read_set = {} /\ tx_status[tx].write_set # {} => Cardinality(tx_status'[tx].write_set) <= Cardinality(tx_status[tx].write_set) 
    \/ tx_status[tx].write_set = {} /\ tx_status[tx].commit_set # {} => Cardinality(tx_status'[tx].commit_set) <= Cardinality(tx_status[tx].commit_set) 
    \/ tx_status[tx].read_set = {} /\ tx_status[tx].write_set # {} => tx_status'[tx].status = "ABORTING"
    \/ tx_status[tx].read_set = {} /\ tx_status[tx].write_set = {} /\ tx_status[tx].commit_set = {})

Evolution_abort(tx) == /\ tx_status[tx].status = "ABORTING"
                       /\ Cardinality(tx_status'[tx].commit_set) <= Cardinality(tx_status[tx].commit_set)

\* Ensures the correct evolution of states 
Correct_evolution == [][\A tx \in TX_ID: Evolution_correct(tx) \/ Evolution_abort(tx)]_vars

\* No prepares when it ends
No_prepare == \A key \in KEY:\A n \in (DOMAIN db[key]): db[key][n].state # "PREPARED"

\* Ensures that if one write commits then all writes of this transaction must commit either
All_commit == \A key \in KEY: \E n \in (DOMAIN db[key]): 
               ((db[key][n].state = "COMMITTED" /\ db[key][n].tx # NOVAL) => \A k \in write_keys[db[key][n].tx]:\E n1 \in (DOMAIN db[k]): db[k][n1].state = "COMMITTED" /\ db[k][n1].tx = db[key][n].tx)

Abort_no_commit == \A tx \in TX_ID: (\E key \in write_keys[tx]: \E entry \in DOMAIN db[key]: db[key][entry].state = "ABORTED" /\ db[key][entry].tx = tx ) => (\A k \in write_keys[tx]:\A n \in DOMAIN db[k]: db[k][n].tx = tx => db[k][n].state = "ABORTED")  

Final_validation == Finished => (All_commit /\ 
                                 Abort_no_commit /\ 
                                 No_prepare)

\* Ensures that all keys on the database can only have one "PREPARED" entry
Only_one_prepare == (\A key \in KEY:\E n \in (DOMAIN db[key]): (db[key][n].state = "PREPARED" => \A n1 \in (DOMAIN db[key]): n1 = n \/ db[key][n1].state # "PREPARED"))

\* Ensures that all operations registred are reflected in the database
All_ops_in_db == \A op \in ops: \E n \in (DOMAIN db[op.key]): 
                                db[op.key][n].val = op.value /\ db[op.key][n].status # "ABORT" 
\* CONSTRAINTS ----------------------------------------------------------------------

Max_time == \A p \in PART: Get_time(p) <= MAX_TIME

================================








