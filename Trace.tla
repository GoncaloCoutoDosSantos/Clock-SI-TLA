---- MODULE Trace ----
EXTENDS TLC,Integers,Sequences

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
    <<(k1 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL]>> @@ k2 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL]>>),
      (t1 :> [status |-> "READ",time |-> NOVAL,key_set |-> READ_KEYS[t1],resp|-><<>>] @@ t2 :> [status |-> "READ",time |-> NOVAL,key_set |-> READ_KEYS[t2],resp|-><<>>]),
      (p1 :> 1 @@ p2 :> 1),
      (t1 :> <<>> @@ t2 :> <<>>)>>,

    <<(k1 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL]>> @@ k2 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL]>>),
      (t1 :> [status |-> "WRITE",time |-> 1,key_set |-> WRITE_KEYS[t1],resp|-><<>>] @@ t2 :> [status |-> "READ",time |-> NOVAL,key_set |-> READ_KEYS[t2],resp|-><<>>]),
      (p1 :> 1 @@ p2 :> 1),
      (t1 :> <<[key |-> k1, op |-> "read", value |-> NOVAL]>> @@ t2 :> <<>>)>>,

    <<(k1 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL]>> @@ k2 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL]>>),
      (t1 :> [status |-> "WRITE",time |-> 1,key_set |-> WRITE_KEYS[t1],resp|-><<>>] @@ t2 :> [status |-> "WRITE",time |-> 1,key_set |-> WRITE_KEYS[t2],resp|-><<>>]),
      (p1 :> 1 @@ p2 :> 1),
      (t1 :> <<[key |-> k1, op |-> "read", value |-> NOVAL]>> @@ t2 :> <<[key |-> k2, op |-> "read", value |-> NOVAL]>>)>>,

    <<(k1 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL]>> @@ 
       k2 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL],
               [val |-> t1,state |-> "PREPARED",timestamp |-> 1,tx |-> t1]>>),
      (t1 :> [status |-> "COMMIT",time |-> 1,key_set |-> WRITE_KEYS[t1],resp|-><<>>] @@ t2 :> [status |-> "WRITE",time |-> 1,key_set |-> WRITE_KEYS[t2],resp|-><<>>]),
      (p1 :> 1 @@ p2 :> 1),
      (t1 :> <<[key |-> k1, op |-> "read", value |-> NOVAL],[key |-> k2, op |-> "write", value |-> t1]>> @@ t2 :> <<[key |-> k2, op |-> "read", value |-> NOVAL]>>)>>,

    <<(k1 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL]>> @@ 
       k2 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL],
               [val |-> t1,state |-> "COMMITTED",timestamp |-> 1,tx |-> t1]>>),
      (t1 :> [status |-> "DONE",time |-> 1,key_set |-> {},resp|-><<>>] @@ t2 :> [status |-> "WRITE",time |-> 1,key_set |-> WRITE_KEYS[t2],resp|-><<>>]),
      (p1 :> 1 @@ p2 :> 1),
      (t1 :> <<[key |-> k1, op |-> "read", value |-> NOVAL],[key |-> k2, op |-> "write", value |-> t1]>> @@ t2 :> <<[key |-> k2, op |-> "read", value |-> NOVAL]>>)>>,

    <<(k1 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL],
               [val |-> t2,state |-> "PREPARED",timestamp |-> 1, tx |-> t2]>> @@ 
       k2 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL],
               [val |-> t1,state |-> "COMMITTED",timestamp |-> 1,tx |-> t1]>>),
      (t1 :> [status |-> "DONE",time |-> 1,key_set |-> {},resp|-><<>>] @@ t2 :> [status |-> "COMMIT",time |-> 1,key_set |-> WRITE_KEYS[t2],resp|-><<>>]),
      (p1 :> 1 @@ p2 :> 1),
      (t1 :> <<[key |-> k1, op |-> "read", value |-> NOVAL],[key |-> k2, op |-> "write", value |-> t1]>> @@ 
       t2 :> <<[key |-> k2, op |-> "read", value |-> NOVAL],[key |-> k1, op |-> "write", value |-> t2]>>)>>,

    <<(k1 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL],
               [val |-> t2,state |-> "COMMITTED",timestamp |-> 1,tx |-> t2]>> @@ 
       k2 :> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |-> NOVAL],
               [val |-> t1,state |-> "COMMITTED",timestamp |-> 1, tx |-> t1]>>),
      (t1 :> [status |-> "DONE",time |-> 1,key_set |-> {},resp|-><<>>] @@ t2 :> [status |-> "DONE",time |-> 1,key_set |-> {},resp|-><<>>]),
      (p1 :> 1 @@ p2 :> 1),
      (t1 :> <<[key |-> k1, op |-> "read", value |-> NOVAL],[key |-> k2, op |-> "write", value |-> t1]>> @@ 
       t2 :> <<[key |-> k2, op |-> "read", value |-> NOVAL],[key |-> k1, op |-> "write", value |-> t2]>>)>>
>>

KEY == {k1,k2}

TX_ID == {t1,t2}

VALUES == {t1,t2}

PART == {p1,p2}

PART_KEY == (p1 :> {k1} @@ p2 :> {k2})

KEY_PART == (k1 :> p1 @@ k2 :> p2)

TIME_DIST == 3

MAX_TIME == 10

Model == INSTANCE Clock_SI

Read == LET
            rec == trace[1]
        IN
            /\ db = rec[1]
            /\ tx_status = rec[2]
            /\ partition_time = rec[3]
            /\ read_keys = READ_KEYS 
            /\ write_keys = WRITE_KEYS
            /\ ops = rec[4]

Read_next == LET
                rec == trace[ind]
            IN
                /\ db' = rec[1]
                /\ tx_status' = rec[2]
                /\ partition_time' = rec[3]
                /\ read_keys' = read_keys
                /\ write_keys' = write_keys
                /\ ops' = rec[4]

Init == ind = 2 /\ Read

Next == ind <= Len(trace) /\ ind' = ind + 1 /\ Read_next

Trace_behaviour == Init /\ [][Next]_vars /\ WF_vars(Next)

Refinement ==  Model!Spec

================================
