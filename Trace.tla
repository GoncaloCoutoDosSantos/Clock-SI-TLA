---- MODULE Trace ----
EXTENDS TLC,FiniteSets,Sequences,Integers,Util

CONSTANTS t1,t2

CONSTANTS k1,k2

CONSTANTS p1,p2

CONSTANTS NOVAL

VARIABLES 
          \* Model variables
          db,             
          tx_status,       
          partition_time,  
          read_keys,     
          write_keys,             
          ops,
          \* trace indice
          ind
          
vars == <<db,tx_status,partition_time,read_keys,write_keys,ops,ind>>

READ_KEYS == (t1 :> {k1} @@ t2 :> {k2})

WRITE_KEYS == (t1 :> {k2} @@ t2 :> {k1})

trace == <<
    [op |-> "read"  , key |->  k1 , value |-> NOVAL, tx |-> t1, time |-> 1],
    [op |-> "read"  , key |->  k2 , value |-> NOVAL, tx |-> t2, time |-> 1],
    [op |-> "write" , key |-> {k2}, value |-> t1   , tx |-> t1, time |-> 1],
    [op |-> "commit", key |-> {k2}, value |-> t1   , tx |-> t1, time |-> 1],
    [op |-> "write" , key |-> {k1}, value |-> t2   , tx |-> t2, time |-> 1],
    [op |-> "commit", key |-> {k1}, value |-> t2   , tx |-> t2, time |-> 1]
>>

log == [trace |-> trace, read_keys |-> (t1 :> {k1} @@ t2 :> {k2}), write_keys |-> (t1 :> {k2} @@ t2 :> {k1})]

KEY == {k1,k2}

TX_ID == {t1,t2}

VALUES == {t1,t2}

PART == {p1,p2}

PART_KEY == (p1 :> {k1} @@ p2 :> {k2})

KEY_PART == (k1 :> p1 @@ k2 :> p2)

TIME_DIST == 3

MAX_TIME == 10

Model == INSTANCE Clock_SI

\* Tranforms a set to a unique sequence 
SetToSeq(s) == CHOOSE f \in [1..Cardinality(s) -> s] : IsInjective(f) 

Max(x,y) == IF x > y THEN x ELSE y

Initial_state_db(set_keys) == 
    [key \in set_keys |-> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL]>>]

Initial_tx_status(set_tx,read_key,write_key) == 
    [tx \in set_tx |-> [status |-> "RUNNING",
                        start_timestamp |-> NOVAL,
                        commit_timestamp |-> NOVAL,
                        read_set |-> read_key[tx],
                        write_set |-> write_key[tx],
                        commit_set |-> write_key[tx]]]

Read_init == 
    /\ db = Initial_state_db(KEY)
    /\ tx_status = Initial_tx_status(TX_ID,log.read_keys,log.write_keys)
    /\ partition_time = [p \in PART |-> 1]
    /\ read_keys = log.read_keys
    /\ write_keys = log.write_keys
    /\ ops = [tx \in TX_ID |-> <<>>]

Read_read(rec) ==
    LET
        start_timestamp == IF tx_status[rec.tx].start_timestamp = NOVAL
                           THEN rec.time
                           ELSE tx_status[rec.tx].start_timestamp
        new_read_set == tx_status[rec.tx].read_set \ {rec.key}
    IN
        /\ rec.op = "read"
        /\ ops' = [ops EXCEPT ![rec.tx] = Append(ops[rec.tx],[op |-> "read",key |-> rec.key,value |-> rec.value,time |-> NOVAL])]
        /\ tx_status' = [tx_status EXCEPT ![rec.tx] = [start_timestamp |-> start_timestamp,read_set |-> new_read_set] @@ tx_status[rec.tx]]
        /\ UNCHANGED <<db,partition_time,read_keys,write_keys>>

Read_write(rec) == 
    LET 
        new_db == [key \in rec.key |-> Append(db[key],[val |-> rec.value,state |-> "PREPARED",timestamp |-> rec.time,tx |-> rec.tx])]
        
        start_timestamp == IF tx_status[rec.tx].start_timestamp = NOVAL
                           THEN rec.time
                           ELSE tx_status[rec.tx].start_timestamp
        commit_timestamp == IF tx_status[rec.tx].commit_timestamp = NOVAL
                            THEN rec.time 
                            ELSE Max(tx_status[rec.tx].commit_timestamp, rec.time)
        new_write_set == tx_status[rec.tx].write_set \ rec.key
    IN
        /\ rec.op = "write"
        /\ ops' = [ops EXCEPT ![rec.tx] = ops[rec.tx] \o SetToSeq({[op |-> "write",key |-> key,value |-> rec.value,time |-> rec.time]: key \in rec.key})]
        /\ tx_status' = [tx_status EXCEPT ![rec.tx] = [start_timestamp |-> start_timestamp,
                                                       commit_timestamp |-> commit_timestamp,
                                                       write_set |-> new_write_set] @@ tx_status[rec.tx]]
        /\ db' = new_db @@ db
        /\ UNCHANGED <<partition_time,read_keys,write_keys>>

Read_commit(rec) == 
    LET 
        commit_timestamp == tx_status[rec.tx].commit_timestamp

        update_entry(entry) == 
            IF entry.state = "PREPARED" /\ entry.tx = rec.tx 
            THEN [state |-> "COMMITTED",timestamp |-> commit_timestamp] @@ entry 
            ELSE entry

        new_db == [key \in rec.key |-> [n \in (DOMAIN db[key]) |-> update_entry(db[key][n])]]
    IN
        /\ rec.op = "commit"
        /\ tx_status' = [tx_status EXCEPT ![rec.tx] = [commit_set |-> tx_status[rec.tx].commit_set \ rec.key] @@ tx_status[rec.tx]]
        /\ db' = new_db @@ db
        /\ UNCHANGED <<ops,partition_time,read_keys,write_keys>>

Read_next == LET
                rec == log.trace[ind]
            IN
                \/ Read_read(rec)
                \/ Read_write(rec)
                \/ Read_commit(rec)

Terminating == ind >= Len(log.trace) /\ UNCHANGED vars

Init == ind = 1 /\ Read_init

Next == (ind <= Len(log.trace) /\ ind' = ind + 1 /\ Read_next) \/ Terminating

Trace_behaviour == Init /\ [][Next]_vars /\ WF_vars(Next)

Refinement ==  Model!Spec

================================
