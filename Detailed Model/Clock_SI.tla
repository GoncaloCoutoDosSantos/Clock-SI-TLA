---- MODULE Clock_SI ----
EXTENDS TLC,FiniteSets,Sequences,Integers,Util

CONSTANTS KEY,       \* Set of all keys
          VALUES,    \* Set of all values
          NOVAL,     \* the value null 
          PART,      \* Number of partitons
          TX_ID,     \* transactions ID's
          TIME_DELTA,\* Max update to time 
          KEY_PART,  \* Function that maps a key to a partition
          PART_KEY   \* Function that maps a partition to a key

ASSUME TIME_DELTA \in SUBSET Nat

ASSUME \A key \in (DOMAIN KEY_PART): key \in PART_KEY[KEY_PART[key]] 

VARIABLES 
\* Partition variables 
          db,         \* Function that represents Key-value database
          inbox,      \* Function that maps a partition to his inbox
          c_status,   \* Function that maps a coordinator of a transaction to is status 
          time,       \* Simulation of real time 
\* Snapshot variables 

          read_keys, \* Function that maps a transaction to a set of keys to read 
          write_keys,\* Function that maps a transaction to a set of keys to write 
          state,     \* Function that maps a transaction to is current state
\* Client-centric variables
          ops

vars_view == <<db,inbox,c_status,time,read_keys,write_keys,state>>
vars      == <<db,inbox,c_status,time,read_keys,write_keys,state,ops>>
vars_snap == <<read_keys,write_keys>>

CC == INSTANCE ClientCentric WITH Keys <- KEY, Values <-  VALUES         
    
\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)
InitialState == [k \in KEY |-> NOVAL]

START_TIMESTAMP == 1

\* Data types --------------------------------------------------------

TIME == 0..99

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
COORDINATOR_STATUS == {"INACTIVE","READ","WRITE"}


\* State needed by a coordinator
\* status -> stores the operation the coordinator is performing
\* key_set -> stores the keys that did not respond yet
\* part -> partition responsible by this transaction
\* time -> start timestamp of the transaction
\* resp -> stores the result of the last operation performed(Write: [KEY -> TIME],Read: [KEY -> VALUE])
COORDINATOR_ENTRY == [status: COORDINATOR_STATUS,key_set:SUBSET KEY,part:PART \union {NOVAL},time:TIME,resp:UNION {[x -> VALUES \union TIME] : x \in SUBSET KEY}]

\* Auxiliar functions --------------------------------------------

SetToSeq(s) == CHOOSE f \in [1..Cardinality(s) -> s] : IsInjective(f) 

\* Retrive the current time 
Get_time(p) == time[p] 

Update_time(p) == \E delta \in TIME_DELTA: time' = [time EXCEPT ![p] = time[p] + delta]

Sync_time(p) == /\ \E p1 \in PART: p # p1 /\ time[p] < time[p1] /\ time' = [time EXCEPT ![p] = time[p1]] 
                /\ UNCHANGED <<c_status, db, inbox, read_keys, state, write_keys>>

Send_msg(set_msg) == LET
                        aux == [p \in PART|-> {m \in set_msg:m.to = p}]
                     IN
                        [p \in PART |-> inbox[p] \union aux[p]]

\* Auxiliar to make a message 
Mk_msg(type,from,to,msg,timestamp,id) == [type |-> type,from |-> from,to |-> to, msg |-> msg, timestamp |-> timestamp,id|->id]


\* Checks if there isn't a write-write conflict 
\* If a there is a version of this key commited then it must have been commited after th start timestamp
\* It can be no prepared version for this key 
Check_key_write(start_timestamp,tx,key) == 
    \A version \in (DOMAIN db[key]):
        /\ (db[key][version].state = "COMMITTED" => db[key][version].timestamp < start_timestamp)
        /\ (db[key][version].state # "PREPARED")

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

Init_part == 
        /\ db = [k \in KEY |-> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |->NOVAL]>>]
        /\ inbox = [p \in PART |-> {}]
        /\ c_status \in [TX_ID -> {[status|->"INACTIVE",part |-> p,time |-> START_TIMESTAMP,key_set |-> {},resp|-><<>>]:p \in PART}]
        /\ time = [p \in PART |-> START_TIMESTAMP]

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


\* set_read - set of keys to be read
\* tx - transaction id
Read(set_read,tx) == 
                LET
                    p == c_status[tx].part
                    parts_msg == {part \in PART: \E k \in set_read: KEY_PART[k] = part} \* set with ids to partitoin to message
                    timestamp == Get_time(p)
                    set_msg == {Mk_msg("Read",p,KEY_PART[key],key,timestamp,tx): key \in set_read} 
                IN
                    /\ c_status[tx].status = "INACTIVE"
                    /\ inbox' = Send_msg(set_msg)
                    /\ c_status' = [c_status EXCEPT ![tx] = [time|->timestamp,status|->"READ",key_set|->set_read,resp|-><<>>] @@ c_status[tx]]
                    /\ Update_time(p)
                    /\ UNCHANGED <<db,ops>>

Distributed_write(set_write,tx) == 
                LET 
                    p == c_status[tx].part
                    keys == DOMAIN set_write
                    parts_msg == {part \in PART: \E k \in keys: KEY_PART[k] = part} \* set with ids to partitoin to message
                    part_write == [part \in parts_msg |-> [key \in (PART_KEY[part] \intersect keys) |-> set_write[key]]]
                    timestamp == c_status[tx].time
                    set_msg == {Mk_msg("Prepare",p,part,part_write[part],timestamp,tx): part \in parts_msg} 
                IN 
                    /\ c_status[tx].status = "INACTIVE"
                    /\ inbox' = Send_msg(set_msg)
                    /\ c_status' = [c_status EXCEPT ![tx] = [status |-> "WRITE",key_set|-> keys,resp|-><<>>] @@ c_status[tx]]
                    /\ UNCHANGED <<db,time,ops>>

Local_write(set_write,tx) == 
                LET
                    p == c_status[tx].part
                    keys == DOMAIN set_write
                    timestamp == c_status[tx].time
                    can_write == \A key \in keys: Check_key_write(timestamp,tx,key)                   
                IN
                    /\ c_status[tx].status = "INACTIVE"
                    /\ Update_time(p)
                    /\ IF can_write 
                       THEN db' = [key \in keys |-> Append(db[key],[val|->set_write[key],timestamp|->timestamp,state|->"COMMITTED",tx|->tx])] @@ db  /\
                            Write_ops(tx,[key \in keys |-> timestamp])
                       ELSE db' = [key \in keys |-> Append(db[key],[val|->set_write[key],timestamp|->timestamp,state|->"ABORTED",tx|->tx])] @@ db  /\
                            Clean_ops(tx)  
                    /\ state' = [state EXCEPT ![tx] = "DONE"]      
                    /\ UNCHANGED <<inbox,c_status>>

\*----------------------------------------------------
\* Mesages received by partition not coordenator

Read_msg(p,msg,my_time) == LET
                        tx == msg.id
                        key == msg.msg
                        new_resp(n) == [k \in {key}|-> db[key][n].val] @@ c_status[tx].resp
                        new_key_set == c_status[tx].key_set \ {key}
                        new_ret(n) == c_status[tx].resp @@ [k \in {key} |-> db[key][n].val]

                        finish_read(n) == 
                            /\ c_status[tx].status = "READ"
                            /\ c_status' = [c_status EXCEPT ![tx] = [status|->"INACTIVE",time |-> START_TIMESTAMP,key_set |-> {},resp|-><<>>] @@ c_status[tx]]
                            /\ state' = [state EXCEPT ![tx] = IF write_keys[tx] # {} THEN "WRITE" ELSE "DONE"]

                        normal_read(n) == 
                            /\ c_status' = [c_status EXCEPT ![tx] = [key_set |-> new_key_set,resp |-> new_resp(n)] @@ c_status[tx]]
                            /\ state' = state
                   IN
                        /\ msg.type = "Read"
                        /\ \E n \in (DOMAIN db[key]): 
                            Check_key_read(msg.timestamp,key,db[key][n]) /\ 
                            Read_ops(tx,key,db[key][n].val) /\
                            IF c_status[tx].key_set = {key} THEN finish_read(n) ELSE normal_read(n)
                        /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                        /\ UNCHANGED <<db>>


Finish_write(p,msg,my_time) == 
                    LET
                        tx == msg.id
                        keys == (DOMAIN c_status[tx].resp) 
                        all_keys == keys \union (DOMAIN msg.msg)
                        times == {c_status[tx].resp[key]: key \in keys} \union {my_time}
                        t == CHOOSE t \in times: \A t1 \in times: t >= t1
                        parts_msg == {part \in PART: \E k \in all_keys: KEY_PART[k] = part} \* set with ids to partitoin to message
                        set_msg(t_max) == {Mk_msg("Commit",p,part,all_keys \intersect PART_KEY[part],t_max,tx):part \in parts_msg}

                        new_inbox(msg_set) == 
                            [part \in (PART \ {p}) |->{m \in msg_set:m.to = part} \union inbox[part]] @@ 
                            [part \in {p}|->(inbox[part]\union{m \in msg_set:m.to = part})\{msg}]
                    IN
                         /\ c_status[tx].status = "WRITE"
                         /\ c_status' = [c_status EXCEPT ![tx] = [status|->"INACTIVE",time |-> START_TIMESTAMP,key_set |-> {},resp|-> <<>>] @@ c_status[tx]]
                         /\ inbox' = new_inbox(set_msg(t))
                         /\ state' = [state EXCEPT ![tx] = "DONE"]


Write_msg(p,msg,my_time) == LET
                        tx == msg.id
                        keys == DOMAIN msg.msg
                        new_resp == [key \in keys |-> my_time] @@ c_status[tx].resp
                        new_key_set == c_status[tx].key_set \ keys

                        normal_write == 
                            /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                            /\ c_status' = [c_status EXCEPT ![tx] = [key_set |-> new_key_set,resp |-> new_resp] @@ c_status[tx]]
                            /\ state' = state
                    IN
                        /\ msg.type = "Prepare"
                        /\ \A key \in keys: Check_key_write(msg.timestamp,msg.id,key)
                        /\ IF c_status[tx].key_set = keys THEN Finish_write(p,msg,my_time) ELSE normal_write
                        /\ db' = [key \in keys |-> Append(db[key],[val|->msg.msg[key],timestamp|->my_time,state|->"PREPARED",tx|->tx])] @@ db 
                        /\ Write_ops(tx,[key \in keys |-> my_time])



Write_abort(p,msg,my_time) == LET
                        tx == msg.id
                        keys == DOMAIN msg.msg
                        all_keys == (c_status[tx].key_set \union (DOMAIN c_status[tx].resp)) \ keys

                        part_msg == {part \in PART: \A k \in all_keys: KEY_PART[k] = part} \* set with ids to partitoin to message
                        part_abort == [part \in part_msg |-> (PART_KEY[part] \intersect all_keys)]
                        set_msg == {Mk_msg("Abort",p,part,part_abort[part],msg.timestamp,msg.id):part \in part_msg}

                        new_inbox(msg_set) == [part \in (PART \ {p}) |->{m \in msg_set:m.to = part} \union inbox[part]] @@ [part \in {p}|->inbox[part]\{msg}]
                      IN 
                        /\ msg.type = "Prepare"
                        /\ ~(\A key \in keys: Check_key_write(msg.timestamp,msg.id,key))
                        /\ db' = [key \in keys |-> Append(db[key],[val|->msg.msg[key],timestamp|->my_time,state|->"ABORTED",tx |-> msg.id])] @@ db
                        /\ inbox' = new_inbox(set_msg)
                        /\ c_status' = [c_status EXCEPT ![tx] = [status|->"INACTIVE",time |-> START_TIMESTAMP,key_set |-> {},resp|-><<>>] @@ c_status[tx]]
                        /\ Clean_ops(tx)
                        /\ state' = [state EXCEPT ![tx] = "DONE"]


Commit_msg(p,msg,my_time) == LET
                        update_entry(entry) == IF entry.state = "PREPARED" THEN 
                                                    [state |-> "COMMITTED",timestamp |-> msg.timestamp] @@ entry 
                                               ELSE entry
                        aux_db == [key \in msg.msg |-> [n \in (DOMAIN db[key]) |-> update_entry(db[key][n])]]
                        new_db == aux_db @@ db
                     IN
                        /\ msg.type = "Commit"
                        /\ \A key \in msg.msg:\E n \in 1..Len(db[key]):db[key][n].state = "PREPARED" /\ db[key][n].tx = msg.id\* Ensures that already as receive the prepared and the acquired the lock
                        /\ db' = new_db
                        /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                        /\ UNCHANGED <<c_status,state,ops>>


Abort_msg(p,msg,my_time) == LET
                        tx == msg.id
                        update_entry(entry) == IF entry.state = "PREPARED" THEN
                                                    [state |-> "ABORTED",timestamp |-> msg.timestamp] @@ entry 
                                               ELSE entry
                        aux_db == [key \in msg.msg |-> [n \in 1..Len(db[key]) |-> update_entry(db[key][n])]]
                    IN
                    /\ msg.type = "Abort"
                    /\ \A key \in msg.msg:\E n \in 1..Len(db[key]): db[key][n].state = "PREPARED" /\ db[key][n].tx = msg.id
                    /\ db' = aux_db @@ db 
                    /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                    /\ Clean_ops(tx)
                    /\ UNCHANGED <<c_status,state>>

\*------------------------------------------------------------------------
\* Message recive by coordinatoor

Recv_msg == LET
                t(p,msg) == IF Get_time(p) > msg.timestamp THEN Get_time(p) ELSE msg.timestamp
                update_t(p,msg) == IF Get_time(p) > msg.timestamp THEN Update_time(p) ELSE \E d_time \in TIME_DELTA:time' = [time EXCEPT ![p] = msg.timestamp + d_time] 
            IN
                \E p \in PART:\E msg \in inbox[p]:
                ((   Abort_msg(p,msg,t(p,msg))
                  \/ Commit_msg(p,msg,t(p,msg)) 
                  \/ Write_abort(p,msg,t(p,msg))
                  \/ Write_msg(p,msg,t(p,msg))
                  \/ Read_msg(p,msg,t(p,msg))) /\ update_t(p,msg)) 
            
                

Next_part ==  Recv_msg /\ UNCHANGED vars_snap

\* Snapshot model --------------------------------------------------------------

Init_snap == /\ read_keys \in [TX_ID -> SUBSET KEY]
             /\ write_keys \in [TX_ID -> SUBSET KEY]
             /\ \A tx \in TX_ID: (read_keys[tx] \union write_keys[tx]) # {}
             /\ state = [t \in TX_ID |-> "READ"]

Start_read(tx) == /\ state[tx] = "READ"
                  /\ read_keys[tx] # {}
                  /\ state' = [state EXCEPT ![tx] = "WAIT_READ"]
                  /\ Read(read_keys[tx],tx)
                  /\ UNCHANGED <<read_keys,write_keys,db,ops>>

Start_read_empty(tx) == /\ state[tx] = "READ"
                        /\ read_keys[tx] = {}
                        /\ state' = [state EXCEPT ![tx] = "WRITE"]
                        /\ UNCHANGED <<read_keys,inbox,write_keys,c_status,time,db,ops>>

Start_write(tx) == LET
                        p == c_status[tx].part
                        flag == (write_keys[tx] \intersect PART_KEY[p]) = write_keys[tx]
                   IN
                   /\ state[tx] = "WRITE"
                   /\ IF flag THEN Local_write([key \in write_keys[tx] |-> tx],tx) 
                      ELSE Distributed_write([key \in write_keys[tx] |-> tx],tx) /\ 
                           state' = [state EXCEPT ![tx] = "WAIT_WRITE"]
                   /\ UNCHANGED <<read_keys,write_keys>>

Terminating == \A tx \in TX_ID: state[tx] = "DONE" /\ UNCHANGED vars

  
Next_snap == ((\E tx \in TX_ID: Start_read(tx) \/ Start_read_empty(tx) \/ Start_write(tx)) \/ Terminating) 

\*---------------------------------------------------------------------------------

Init == Init_part /\ Init_snap /\ ops = [tx \in TX_ID |-> <<>>] 

Next == Next_snap \/ Next_part 

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Type_OK == /\ state \in [TX_ID -> {"READ","WAIT_READ","WRITE","WAIT_WRITE","DONE"}] 
           /\ write_keys \in [TX_ID -> SUBSET KEY]
           /\ read_keys \in [TX_ID -> SUBSET KEY]
           /\ time \in TIMESTAMP
           /\ c_status \in [TX_ID -> COORDINATOR_ENTRY]
           /\ PART_KEY \in [PART -> SUBSET KEY]
           /\ KEY_PART \in [KEY -> PART]
           /\ db \in [KEY -> Seq(DB_ENTRY)]

SnapshotIsolation == (\A tx \in TX_ID: state[tx] = "DONE") => CC!SnapshotIsolation(InitialState, Range(ops))

\* Ensures that eventually all transactions end 
All_finish == <> (\A tx \in TX_ID:state[tx] = "DONE")

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

Final_validation == (\A tx \in TX_ID:state[tx] = "DONE") => (All_commit /\ 
                                                             All_abort /\ 
                                                             All_entry /\ 
                                                             No_prepare)

Only_prepare == [](\A key \in KEY:\E n \in (DOMAIN db[key]): (db[key][n].state = "PREPARED" => \A n1 \in (DOMAIN db[key]): n1 = n \/ db[key][n1].state # "PREPARED"))
================================








