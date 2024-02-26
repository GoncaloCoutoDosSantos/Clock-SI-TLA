---- MODULE Clock_SI ----
EXTENDS TLC,Naturals,Sequences

CONSTANTS KEY,       \* Set of all keys
          VALUES,    \* Set of all values
          NOVAL,     \* the value null 
          PART,      \* Number of partitons
          TX_ID,     \* transactions ID's
          TIME_DELTA,\* Max update to time 
          KEY_PART,  \* Function that maps a key to a partition
          PART_KEY   \* Function that maps a partition to a key

ASSUME TIME_DELTA \in SUBSET Nat

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

vars      == <<db,inbox,c_status,time,read_keys,write_keys,state,ops>>
vars_snap == <<read_keys,write_keys>>

CC == INSTANCE ClientCentric WITH Keys <- KEY, Values <- TX_ID \union {NOVAL}          
    
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
COORDINATOR_STATUS == {"INACTIVE","READ","WRITE","COMPLETE"}


\* State needed by a coordinator
\* status -> stores the operation the coordinator is performing
\* key_set -> stores the keys that did not respond yet
\* part -> partition responsible by this transaction
\* time -> start timestamp of the transaction
\* resp -> stores the result of the last operation performed(Write: {"OK","ABORT"},Read: [KEY -> VALUE])
COORDINATOR_ENTRY == [status: COORDINATOR_STATUS,key_set:SUBSET KEY,part:PART \union {NOVAL},time:TIME,resp:UNION {[x -> VALUES] : x \in SUBSET KEY}]

\* Auxiliar functions --------------------------------------------

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

Init_part == 
        /\ db = [k \in KEY |-> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |->NOVAL]>>]
        /\ inbox = [p \in PART |-> {}]
        /\ \E p \in PART:
            c_status = [t \in TX_ID |-> [status|->"INACTIVE",part|-> p,time |-> START_TIMESTAMP,key_set |-> {},resp|-><<>>]]
        /\ time = [p \in PART |-> START_TIMESTAMP]

Read_snap(tx,ret) == /\ state[tx] = "WAIT_READ"
                     /\ state' = [state EXCEPT ![tx] = IF write_keys[tx] # {} THEN "WRITE" ELSE "DONE"]
                     /\ ops' = ops \union {rOp(key,ret.ret[key]):key \in read_keys[tx]}
              
Write_snap_success(tx) == 
                    /\ state' = [state EXCEPT ![tx] = "DONE"]   
                    /\ ops' = ops \union {wOp(key,tx):key \in write_keys[tx]}

Write_snap_abort(tx) == 
                    /\ state' = [state EXCEPT ![tx] = "DONE"]
                    /\ ops' = ops

Write_snap(tx,ret) == 
                \*/\ state[tx] = "WAIT_WRITE"
                /\ IF ret.ret = "OK" THEN
                        Write_snap_abort(tx)
                    ELSE 
                        Write_snap_success(tx)

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
                    /\ c_status' = [c_status EXCEPT ![tx] = [time|->timestamp,status|->"READ",tx|->tx,key_set|->set_read,resp|-><<>>] @@ c_status[tx]]
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
                    /\ c_status' = [c_status EXCEPT ![tx] = [status |-> "WRITE",tx |-> tx,key_set|-> keys,resp|-><<>>] @@ c_status[tx]]
                    /\ UNCHANGED <<db,time,ops>>

Local_write(set_write,tx) == 
                LET
                    p == c_status[tx].part
                    keys == DOMAIN set_write
                    my_time == Get_time(p)
                    can_write == \A key \in keys: Check_key_write(my_time,tx,key)                   
                IN
                    /\ c_status[tx].status = "INACTIVE"
                    /\ Update_time(p)
                    /\ IF can_write 
                       THEN db' = [key \in keys |-> Append(db[key],[val|->set_write[key],timestamp|->my_time,state|->"COMMITTED",tx|->tx])] @@ db  /\
                            Write_snap(tx,[type|-> "WRITE",ret|->"OK"])
                       ELSE db' = [key \in keys |-> Append(db[key],[val|->set_write[key],timestamp|->my_time,state|->"ABORTED",tx|->tx])] @@ db  /\
                            Write_snap(tx,[type|-> "WRITE",ret|->"ABORT"])
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
                            /\ c_status' = [c_status EXCEPT ![tx] = [status|->"INACTIVE",time |-> START_TIMESTAMP,tx|-> NOVAL,key_set |-> {},resp|-><<>>] @@ c_status[tx]]
                            /\ Read_snap(tx,[type |-> "READ",ret|->new_ret(n)])

                        normal_read(n) == 
                            /\ c_status' = [c_status EXCEPT ![tx] = [key_set |-> new_key_set,resp |-> new_resp(n)] @@ c_status[tx]]
                            /\ state' = state
                            /\ ops' = ops
                   IN
                        /\ msg.type = "Read"
                        /\ \E n \in (DOMAIN db[key]): 
                            Check_key_read(msg.timestamp,key,db[key][n]) /\ 
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
                         /\ c_status' = [c_status EXCEPT ![tx] = [status|->"INACTIVE",time |-> START_TIMESTAMP,tx|-> NOVAL,key_set |-> {},resp|-> <<>>] @@ c_status[tx]]
                         /\ inbox' = new_inbox(set_msg(t))
                         /\ Write_snap(tx,[type|-> "WRITE",ret|->"OK"])


Write_msg(p,msg,my_time) == LET
                        tx == msg.id
                        keys == DOMAIN msg.msg
                        new_resp == [key \in keys |-> my_time] @@ c_status[tx].resp
                        new_key_set == c_status[tx].key_set \ keys

                        normal_write == 
                            /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                            /\ c_status' = [c_status EXCEPT ![tx] = [key_set |-> new_key_set,resp |-> new_resp] @@ c_status[tx]]
                            /\ state' = state
                            /\ ops' = ops
                    IN
                        /\ msg.type = "Prepare"
                        /\ \A key \in keys: Check_key_write(msg.timestamp,msg.id,key)
                        /\ IF c_status[tx].key_set = keys THEN Finish_write(p,msg,my_time) ELSE normal_write
                        /\ db' = [key \in keys |-> Append(db[key],[val|->msg.msg[key],timestamp|->my_time,state|->"PREPARED",tx|->msg.id])] @@ db 



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
                        /\ Write_snap(tx,[type|-> "WRITE",ret|->"ABORT"])
                        /\ c_status' = [c_status EXCEPT ![tx] = [status|->"INACTIVE",time |-> START_TIMESTAMP,key_set |-> {},resp|-><<>>] @@ c_status[tx]]

\* TODO: remove 
Commit_msg(p,msg,my_time) == LET
                        update_entry(entry) == IF entry.state = "PREPARED" THEN 
                                                    [state |-> "COMMITTED",timestamp |-> msg.timestamp] @@ entry 
                                               ELSE entry
                        aux_db == [key \in msg.msg |-> [n \in (DOMAIN db[key]) |-> update_entry(db[key][n])]]
                        new_db == aux_db @@ db
                     IN
                        /\ msg.type = "Commit"
                        /\ \A key \in msg.msg:\E n \in 1..Len(db[key]):db[key][n].state = "PREPARED" \* If it fails something is wrong
                        /\ db' = new_db
                        /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                        /\ UNCHANGED <<c_status,state,ops>>

\* TODO: remove 
Abort_msg(p,msg,my_time) == LET
                        update_entry(entry) == IF entry.state = "PREPARED" THEN
                                                    [state |-> "ABORTED",timestamp |-> msg.timestamp] @@ entry 
                                               ELSE entry
                        aux_db == [key \in msg.msg |-> [n \in 1..Len(db[key]) |-> update_entry(db[key][n])]]
                    IN
                    /\ msg.type = "Abort"
                    /\ \A key \in msg.msg:\E n \in 1..Len(db[key]): db[key][n].state = "PREPARED"
                    /\ db' = aux_db @@ db 
                    /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                    /\ UNCHANGED <<c_status,state,ops>>

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

Init == Init_part /\ Init_snap /\ ops = {}

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

SnapshotIsolation == (\A tx \in TX_ID: state[tx] = "DONE") => CC!SnapshotIsolation(InitialState, ops)

All_finish == <> (\A tx \in TX_ID:state[tx] = "DONE")

All_entry == <> [](\A key \in KEY: \A entry \in (DOMAIN db[key]): db[key][entry].state # "PREPARED")

================================







