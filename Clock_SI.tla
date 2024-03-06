---- MODULE Clock_SI ----
EXTENDS TLC,Naturals,Sequences,Integers

CONSTANTS KEY,       \* Set of all keys
          VALUES,    \* Set of all values
          NOVAL,     \* the value null 
          PART,      \* Number of partitons
          TX_ID,     \* transactions ID's
          TIME_DIST ,\* Max update to time 
          KEY_PART,  \* Function that maps a key to a partition
          PART_KEY,  \* Function that maps a partition to a key
          MAX_TIME   \* Max time value

ASSUME \A key \in (DOMAIN KEY_PART): key \in PART_KEY[KEY_PART[key]] 

ASSUME TIME_DIST > 0

VARIABLES 
\* Partition variables 
          db,             \* Function that represents Key-value database
          tx_status,      \* Function that maps a coordinator of a transaction to is status 
          partition_time, \* Simulation of real time 
\* Snapshot variables 

          read_keys,      \* Function that maps a transaction to a set of keys to read 
          write_keys,     \* Function that maps a transaction to a set of keys to write 
\* Client-centric variables
          ops

vars_view == <<db,tx_status,partition_time,read_keys,write_keys>>
vars      == <<db,tx_status,partition_time,read_keys,write_keys,ops>>
vars_snap == <<read_keys,write_keys,partition_time>>

CC == INSTANCE ClientCentric WITH Keys <- KEY, Values <-  VALUES         
    
\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)
InitialState == [k \in KEY |-> NOVAL]

START_TIMESTAMP == 1

\* Data types --------------------------------------------------------

TIME == Nat

TIMESTAMP == [PART -> TIME]

\* Possible states for a database entry
STATE_ENTRY == {"COMMITTED","PREPARED","ABORTED"}

\* Defenition of a database entry
\* val -> value associated to the key
\* state -> state of the entry
\* timestamp -> is only defined when state changes to "COMMITTED"
\* tx -> transaction id responsible by the write
DB_ENTRY == [val:VALUES \union {NOVAL},state:STATE_ENTRY,timestamp:TIME,tx:TX_ID \union {NOVAL}]

\* Possible states for a coordinator

TRANSACTION_STATUS == {"READ","WRITE","COMMIT","ABORT","DONE"}


\* State needed by a transaction
\* status -> stores the current status of the transaction 
\* key_set -> set of keys that lacks the current action
\* time -> start timestamp in case transaction state is "READ" or "WRITE", or commit timestamp in orther states
\* resp -> stores the result of the last operation performed(Write: [KEY -> TIME],Read: [KEY -> VALUE])
TRANSACTION_ENTRY == [status: TRANSACTION_STATUS,key_set:SUBSET KEY,time:TIME \union {NOVAL},resp:UNION {[x -> VALUES] : x \in SUBSET KEY}]

\* Auxiliar functions --------------------------------------------

Abs(n) == IF n < 0 THEN -n ELSE n

\* Retrive the current time 
Get_time(p) == partition_time[p] 

Update_time == /\ \E p \in PART: partition_time' = [partition_time EXCEPT ![p] = partition_time[p] + 1] /\ (\A p1 \in PART: Abs(partition_time[p] + 1 - partition_time[p1]) < TIME_DIST) 
               /\ UNCHANGED <<db,tx_status,read_keys,write_keys,ops>>

\* Checks if there is a conflict write or if already as recive an abort message
\* if commited the commit timestamp must be lower
\* if aborted then the transaction must be different
\* if there is a entry in prepared state then it aborts 
Check_key_write(timestamp,tx,key) == \A n \in (DOMAIN db[key]):
                                      \/ (db[key][n].state = "COMMITTED" /\ db[key][n].timestamp < timestamp) 
                                      \/ (db[key][n].state = "ABORTED" /\ db[key][n].tx # tx)
                                      \/ (db[key][n].state # "PREPARED") 

\* Checks if the entry choosen has a valid timestamp and if it is committed
\* then compares to all orther entrys to verify it is the latest entry available to that timestamp
\* It returns false if there is entry in committing state with greter timestamp that are valid choises
Check_key_read(timestamp,key,entry) == /\ timestamp > entry.timestamp
                                       /\ entry.state = "COMMITTED"
                                       /\ \A n \in (DOMAIN db[key]):
                                         ((entry.timestamp > db[key][n].timestamp /\ db[key][n].timestamp < timestamp) \/ 
                                           db[key][n] = entry \/
                                           db[key][n].timestamp >= timestamp \/ 
                                           db[key][n].state = "ABORTED")

\*  -----------------------------------------------------------------------------------
\* Auxiliar predicates to change the variable ops 

Read_ops(tx,ret) == 
                     /\ ops' = ops \union {rOp(key,ret[key]):key \in read_keys[tx]}
              
Write_ops_success(tx) == 
                    /\ ops' = ops \union {wOp(key,tx):key \in write_keys[tx]}

Write_ops_abort(tx) == 
                    /\ ops' = ops

Write_ops(tx,ret) == 
                /\ IF ret = "OK" THEN
                        Write_ops_abort(tx)
                    ELSE 
                        Write_ops_success(tx)

\*---------------------------------------------------- 

Read(tx) == \E key \in tx_status[tx].key_set:
        LET 
            p == KEY_PART[key]
            s_time == IF tx_status[tx].time = NOVAL 
                      THEN Get_time(p)
                      ELSE tx_status[tx].time
            new_resp(n) == [k \in {key} |-> db[key][n].val] @@ tx_status[tx].resp
            new_key_set == tx_status[tx].key_set \ {key}
            new_ret(n) == tx_status[tx].resp @@ [k \in {key} |-> db[key][n].val]

            finish_read(n) == 
                LET
                    n_status == IF write_keys[tx] # {} THEN "WRITE" ELSE "DONE"
                IN
                    /\ tx_status' = [tx_status EXCEPT ![tx] = [status |-> n_status,key_set |-> write_keys[tx],resp|-><<>>,time |-> s_time] @@ tx_status[tx]]
                    /\ Read_ops(tx,new_ret(n))

            normal_read(n) == 
                /\ tx_status' = [tx_status EXCEPT ![tx] = [key_set |-> new_key_set,resp |-> new_resp(n),time |-> s_time] @@ tx_status[tx]]
                /\ ops' = ops
        IN
            /\ s_time >= Get_time(p) \* Eunsures that the start timestamp isn't in the future
            /\ tx_status[tx].status = "READ" 
            /\ \E n \in (DOMAIN db[key]):
                 Check_key_read(s_time,key,db[key][n]) /\
                 IF tx_status[tx].key_set = {key} THEN finish_read(n) ELSE normal_read(n)
            /\ UNCHANGED <<db>>


Write(tx) == \E p \in {KEY_PART[k]:k \in tx_status[tx].key_set}:
      LET
         s_time == IF tx_status[tx].time = NOVAL 
                   THEN Get_time(p)
                   ELSE tx_status[tx].time
         keys == PART_KEY[p] \intersect tx_status[tx].key_set 
         my_time == Get_time(p)
         new_resp == [key \in keys |-> my_time] @@ tx_status[tx].resp
         new_key_set == tx_status[tx].key_set \ keys

         times == {tx_status[tx].resp[key]: key \in DOMAIN tx_status[tx].resp} \union {my_time}
         t == CHOOSE t \in times: \A t1 \in times: t >= t1

         normal_write == 
             /\ tx_status' = [tx_status EXCEPT ![tx] = [key_set |-> new_key_set,resp |-> new_resp,time |-> s_time] @@ tx_status[tx]]
             /\ ops' = ops

         finish_write == 
             /\ tx_status' = [tx_status EXCEPT ![tx] = [status|->"COMMIT",time |-> t,key_set |-> write_keys[tx],resp|-> <<>>] @@ tx_status[tx]]
             /\ Write_ops(tx,"OK")
      IN
         /\ s_time >= Get_time(p) \* Eunsures that the start timestamp isn't in the future
         /\ tx_status[tx].status = "WRITE"
         /\ \A key \in keys: Check_key_write(s_time,tx,key)
         /\ IF tx_status[tx].key_set = keys THEN finish_write ELSE normal_write
         /\ db' = [key \in keys |-> Append(db[key],[val|->tx,timestamp|->my_time,state|->"PREPARED",tx|->tx])] @@ db 



Abort_write(tx) == \E p \in {KEY_PART[k]:k \in tx_status[tx].key_set}:
                      LET
                        s_time == IF tx_status[tx].time = NOVAL 
                                  THEN Get_time(p)
                                  ELSE tx_status[tx].time
                        keys == PART_KEY[p] \intersect tx_status[tx].key_set 
                        abort_keys == (tx_status[tx].key_set \union (DOMAIN tx_status[tx].resp)) \ keys
                        new_status == IF abort_keys = {} THEN "DONE" ELSE "ABORT"
                        my_time == Get_time(p)

                      IN 
                        /\ s_time >= Get_time(p) 
                        /\ tx_status[tx].status = "WRITE"
                        /\ ~(\A key \in keys: Check_key_write(my_time,tx,key))
                        /\ db' = [key \in keys |-> Append(db[key],[val|->tx,timestamp|->my_time,state|->"ABORTED",tx |-> tx])] @@ db
                        /\ Write_ops(tx,"ABORT")
                        /\ tx_status' = [tx_status EXCEPT ![tx] = [status|->new_status,time |-> my_time,key_set |-> abort_keys,resp|-><<>>] @@ tx_status[tx]]


Commit(tx) == \E p \in {KEY_PART[k]:k \in tx_status[tx].key_set}:
                     LET
                        keys == PART_KEY[p] \intersect tx_status[tx].key_set

                        update_entry(entry) == IF entry.state = "PREPARED" THEN 
                                                    [state |-> "COMMITTED",timestamp |-> tx_status[tx].time] @@ entry 
                                               ELSE entry
                        aux_db == [key \in keys |-> [n \in (DOMAIN db[key]) |-> update_entry(db[key][n])]]
                        new_db == aux_db @@ db

                        new_key_set == tx_status[tx].key_set \ keys
                        new_status == IF new_key_set = {} THEN "DONE" ELSE "COMMIT"
                     IN
                        /\ tx_status[tx].status = "COMMIT" 
                        /\ \A key \in keys:\E n \in 1..Len(db[key]):db[key][n].state = "PREPARED" /\ db[key][n].tx = tx\* Ensures that already as receive the prepared and the acquired the lock
                        /\ db' = new_db
                        /\ tx_status' = [tx_status EXCEPT ![tx] = [key_set |-> new_key_set, status |-> new_status] @@ tx_status[tx]]
                        /\ UNCHANGED <<ops>>


Abort(tx) == \E p \in {KEY_PART[k]:k \in tx_status[tx].key_set}:
                    LET
                        my_time == tx_status[tx].time
                        keys == PART_KEY[p] \intersect tx_status[tx].key_set
                        preped_keys == {key \in keys: \E n \in (DOMAIN db[key]): db[key][n].state = "PREPARED" /\ db[key][n].tx = tx}

                        update_entry(entry) == IF entry.state = "PREPARED" THEN
                                                    [state |-> "ABORTED",timestamp |-> tx_status[tx].time] @@ entry 
                                               ELSE entry
                        preped_db == [key \in preped_keys |-> [n \in (DOMAIN db[key]) |-> update_entry(db[key][n])]]
                        orthers_db == [key \in (keys \ preped_keys) |-> Append(db[key],[val|->tx,timestamp|->my_time,state|->"ABORTED",tx |-> tx])]
                        new_db == (preped_db @@ orthers_db) @@ db

                        new_key_set == tx_status[tx].key_set \ keys
                        new_status == IF new_key_set = {} THEN "DONE" ELSE "ABORT"
                    IN
                    /\ tx_status[tx].status = "ABORT"
                    /\ db' = new_db
                    /\ tx_status' = [tx_status EXCEPT ![tx] = [key_set |-> new_key_set, status |-> new_status] @@ tx_status[tx]]
                    /\ UNCHANGED <<ops>>

\*------------------------------------------------------------------------
\* Message recive by coordinatoor

Next_action == /\ UNCHANGED vars_snap 
               /\ \E tx \in TX_ID:
                 ((   Abort(tx)
                   \/ Commit(tx) 
                   \/ Abort_write(tx)
                   \/ Write(tx)
                   \/ Read(tx)))  
            
Terminating == \A tx \in TX_ID: tx_status[tx].status = "DONE" /\ UNCHANGED vars

\*---------------------------------------------------------------------------------

Init == 
        /\ read_keys \in [TX_ID -> SUBSET KEY]
        /\ write_keys \in [TX_ID -> SUBSET KEY]
        /\ \A tx \in TX_ID: (read_keys[tx] \union write_keys[tx]) # {}
        /\ db = [k \in KEY |-> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |->NOVAL]>>]
        /\ tx_status = [tx \in TX_ID |-> [status|->IF read_keys[tx] = {} THEN "WRITE" ELSE "READ",time |-> NOVAL,key_set |-> IF read_keys[tx] = {} THEN write_keys[tx] ELSE read_keys[tx],resp|-><<>>]]
        /\ partition_time = [p \in PART |-> START_TIMESTAMP]
        /\ ops = {}

Next == Next_action \/ Terminating \/ Update_time

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


\*PROPERTYS ---------------------------------------------------------------------- 

Type_OK == /\ write_keys \in [TX_ID -> SUBSET KEY]
           /\ read_keys \in [TX_ID -> SUBSET KEY]
           /\ partition_time \in TIMESTAMP
           /\ tx_status \in [TX_ID -> TRANSACTION_ENTRY]
           /\ PART_KEY \in [PART -> SUBSET KEY]
           /\ KEY_PART \in [KEY -> PART]
           /\ db \in [KEY -> Seq(DB_ENTRY)]
           /\ ops \in SUBSET CC!Operation 

SnapshotIsolation == ((\A tx \in TX_ID: tx_status[tx].status = "DONE") /\ (\A p \in PART: Get_time(p) >= MAX_TIME) ) => CC!SnapshotIsolation(InitialState, ops)

\* Ensures that eventually all transactions end 
All_finish == <> (\A tx \in TX_ID:tx_status[tx].status = "DONE")

\* No prepares when it ends
No_prepare == \A key \in KEY:\A n \in (DOMAIN db[key]): db[key][n] # "PREPARED"

\* Ensures that all writes have a entry
All_entry == \A tx \in TX_ID: \A key \in write_keys[tx]: \E n \in (DOMAIN db[key]): db[key][n].tx = tx /\ db[key][n].state # "PREPARED"

\* Ensures that if one write aborts then all writes of this transaction must abort either
All_abort == \A key \in KEY: \E n \in (DOMAIN db[key]): 
            (db[key][n].state = "ABORTED" => \A k \in write_keys[db[key][n].tx]:\E n1 \in (DOMAIN db[k]): db[k][n1].state = "ABORTED" /\ db[k][n1].tx = db[key][n].tx)

\* Ensures that if one write commits then all writes of this transaction must commit either
All_commit == \A key \in KEY: \E n \in (DOMAIN db[key]): 
               (db[key][n].state = "COMMITTED" => \A k \in write_keys[db[key][n].tx]:\E n1 \in (DOMAIN db[k]): db[k][n1].state = "COMMITTED" /\ db[k][n1].tx = db[key][n].tx)

Final_validation == (\A tx \in TX_ID:tx_status[tx].status = "DONE") => (All_commit /\ 
                                                             All_abort /\ 
                                                             All_entry /\ 
                                                             No_prepare)

Only_prepare == [](\A key \in KEY:\E n \in (DOMAIN db[key]): (db[key][n].state = "PREPARED" => \A n1 \in (DOMAIN db[key]): n1 = n \/ db[key][n1].state # "PREPARED"))

All_ops_in_db == \A op \in ops: \E n \in (DOMAIN db[op.key]): 
                                db[op.key][n].val = op.value /\ db[op.key][n].status # "ABORT" 
\* CONSTRAINTS ----------------------------------------------------------------------

Max_time == \A p \in PART: Get_time(p) <= MAX_TIME

================================








