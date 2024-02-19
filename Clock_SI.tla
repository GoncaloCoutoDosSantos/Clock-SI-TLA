---- MODULE Clock_SI ----
EXTENDS TLC,Naturals,Sequences

CONSTANTS KEY,       \* Set of all keys
          VALUES,    \* Set of all values
          NOVAL,     \* the value null 
          PART,      \* Number of partitons
          TX_ID,     \* transactions ID's
          TIME_DELTA \* Max update to time 


VARIABLES 
\* Partition variables 
          db,         \* Function that represents Key-value database
          inbox,      \* Function that maps a partition to his inbox
          key_part,   \* Function that maps a key to a partition  
          part_key,   \* Function that maps a partition to a key
          c_status,   \* Function that maps a coordinator of a transaction to is status 
          time,       \* Simulation of real time 
\* Snapshot variables 

          snapshot,  \* Function that maps a transaction to a snapshot
          read_keys, \* Function that maps a transaction to a set of keys to read 
          write_keys,\* Function that maps a transaction to a set of keys to write 
          state,     \* Function that maps a transaction to is current state
\* common to both models
            
          result    \* Funtion that maps a transactio to the result of the last operation

vars      == <<db,inbox,key_part,part_key,c_status,time,snapshot,read_keys,write_keys,state,result>>
vars_part == <<db,key_part,part_key>>
vars_snap == <<snapshot,read_keys,write_keys,state >>

TIMESTAMP == Nat

START_TIMESTAMP == 1

\* Possible states for a database entry
STATE_ENTRY == {"COMMITTED","PREPARED","ABORTED"}

\* Defenition of a database entry
\* val -> value associated to the key
\* state -> state of the entry
\* timestamp -> is only defined when state changes to "COMMITTED"
\* tx -> transaction id responsible by the write
DB_ENTRY == [val:VALUES \union {NOVAL},state:STATE_ENTRY,timestamp:TIMESTAMP,tx:TX_ID \union {NOVAL}]

\* Possible states for a coordinator
COORDINATOR_STATUS == {"INACTIVE","READ","WRITE","COMPLETE"}

\* State needed by a coordinator
\* status -> stores the operation the coordinator is performing
\* key_set -> stores the keys that did not respond yet
\* part -> partition responsible by this transaction
\* time -> start timestamp of the transaction
\* resp -> stores the result of the last operation performed(Write: {"OK","ABORT"},Read: [KEY -> VALUE])
COORDINATOR_ENTRY == [status: COORDINATOR_STATUS,key_set:SUBSET KEY,part:PART \union {NOVAL},time:TIMESTAMP,resp:[KEY->VALUES \union {NOVAL,"OK","ABORT"}]]

Init_part == 
        /\ db = [k \in KEY |-> <<[val |-> NOVAL,state |-> "COMMITTED",timestamp |-> 0,tx |->NOVAL]>>]
        /\ inbox = [p \in PART |-> {}]
        /\ key_part \in [KEY -> PART] /\ (\A p \in PART: \E k \in KEY: key_part[k] = p)
        /\ part_key = [p \in PART |-> {k \in KEY: key_part[k] = p}]
        /\ c_status = [t \in TX_ID |-> [status|->"INACTIVE",part|->NOVAL,time |-> START_TIMESTAMP,key_set |-> {},resp|-><<>>]]
        /\ time = START_TIMESTAMP

\* Retrive the current time 
Get_time(p) == time

Update_time(p) == \E delta \in 1..TIME_DELTA: time' = time + delta

Send_msg(set_msg) == LET
                        aux == [p \in PART|-> {m \in set_msg:m.to = p}]
                     IN
                        [p \in PART |-> inbox[p] \union aux[p]]

\* Auxiliar to make a message 
Mk_msg(type,from,to,msg,timestamp,id) == [type |-> type,from |-> from,to |-> to, msg |-> msg, timestamp |-> timestamp,id|->id]

Start_tx(tx) == \E p \in PART:
                /\ c_status' = [c_status EXCEPT ![tx] = [part |-> p,time |-> Get_time(p)] @@ c_status[tx]]
                /\ UNCHANGED <<db,inbox,key_part,part_key,time,result>>
                
\* set_read - set of keys to be read
\* tx - transaction id
Read(set_read,tx) == 
                LET
                    p == c_status[tx].part
                    parts_msg == {part \in PART: \E k \in set_read: key_part[k] = part} \* set with ids to partitoin to message
                    timestamp == c_status[tx].time
                    set_msg == {Mk_msg("Read",p,key_part[key],key,timestamp,tx): key \in set_read} 
                IN
                    /\ c_status[tx].status = "INACTIVE"
                    /\ inbox' = Send_msg(set_msg)
                    /\ c_status' = [c_status EXCEPT ![tx] = [status|->"READ",tx|->tx,key_set|->set_read,resp|-><<>>] @@ c_status[tx]]
                    /\ Update_time(p)
                    /\ UNCHANGED <<db,key_part,part_key,result>>

\* set_write - Function that maps the key to the values to write
\* tx - transaction id
Write(set_write,tx) == 
                LET 
                    p == c_status[tx].part
                    keys == DOMAIN set_write
                    parts_msg == {part \in PART: \E k \in keys: key_part[k] = part} \* set with ids to partitoin to message
                    part_write == [part \in parts_msg |-> [key \in (part_key[part] \intersect keys) |-> set_write[key]]]
                    timestamp == c_status[tx].time
                    set_msg == {Mk_msg("Prepare",p,part,part_write[part],timestamp,tx): part \in parts_msg} 
                IN 
                    /\ c_status[tx].status = "INACTIVE"
                    /\ inbox' = Send_msg(set_msg)
                    /\ c_status' = [c_status EXCEPT ![tx] = [status |-> "WRITE",tx |-> tx,key_set|-> keys,resp|-><<>>] @@ c_status[tx]]
                    /\ Update_time(p)
                    /\ UNCHANGED <<db,key_part,part_key,result>>
                                
\*----------------------------------------------------
\* Mesages received by partition not coordenator

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

Read_msg(p,msg) == LET
                        tx == msg.id
                        key == msg.msg
                        new_resp(n) == [k \in {key}|-> db[key][n].val] @@ c_status[tx].resp
                        new_key_set == c_status[tx].key_set \ {key}
                   IN
                        /\ msg.type = "Read"
                        /\ c_status[tx].key_set # {key}
                        /\ \E n \in (DOMAIN db[key]): 
                            Check_key_read(msg.timestamp,key,db[key][n]) /\ 
                            c_status' = [c_status EXCEPT ![tx] = [key_set |-> new_key_set,resp |-> new_resp(n)] @@ c_status[tx]]
                        /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                        /\ Update_time(p)
                        /\ UNCHANGED <<db,key_part,part_key,result>>

Finish_read(p,msg) == 
                    LET
                        tx == msg.id
                        key == msg.msg
                        new_ret(n) == c_status[tx].resp @@ [k \in {key} |-> db[key][n].val]
                    IN
                        /\ c_status[tx].status = "READ"
                        /\ c_status[tx].key_set = {key}
                        /\ msg.type = "Read"
                        /\ \E n \in (DOMAIN db[key]): 
                            Check_key_read(msg.timestamp,key,db[key][n]) /\ 
                            result' = [result EXCEPT ![tx] = result[tx] \union {[type|-> "READ",ret|-> new_ret(n)]}]

                        /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                        /\ c_status' = [c_status EXCEPT ![tx] = [status|->"INACTIVE",time |-> START_TIMESTAMP,tx|-> NOVAL,key_set |-> {},resp|-><<>>] @@ c_status[tx]]
                        /\ Update_time(p)
                        /\ UNCHANGED <<db,key_part,part_key>>



\* Checks if there is a conflict write or if already as recive an abort message
\* if commited the commit timestamp must be lower
\* if aborted then the transaction must be different
\* if there is a entry in prepared state then it aborts 
Check_key_write(timestamp,tx,key) == \A n \in (DOMAIN db[key]):
                                      \/ (db[key][n].state = "COMMITTED" /\ db[key][n].timestamp < timestamp) 
                                      \/ (db[key][n].state = "ABORTED" /\ db[key][n].tx # tx)
                                      \/ (db[key][n].state # "PREPARED") 

Write_msg(p,msg) == LET
                        tx == msg.id
                        keys == DOMAIN msg.msg
                        my_time == Get_time(p)
                        new_resp == [key \in keys |-> my_time] @@ c_status[tx].resp
                        new_key_set == c_status[tx].key_set \ keys
                    IN
                        /\ msg.type = "Prepare"
                        /\ \A key \in keys: Check_key_write(msg.timestamp,msg.id,key)
                        /\ db' = [key \in keys |-> Append(db[key],[val|->msg.msg[key],timestamp|->my_time,state|->"PREPARED",tx|->msg.id])] @@ db 
                        /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                        /\ c_status' = [c_status EXCEPT ![tx] = [key_set |-> new_key_set,resp |-> new_resp] @@ c_status[tx]]
                        /\ Update_time(p)
                        /\ UNCHANGED <<key_part,part_key,result>>

Write_abort(p,msg) == LET
                        tx == msg.id
                        keys == DOMAIN msg.msg
                        my_time == Get_time(p)
                        all_keys == (c_status[tx].key_set \union (DOMAIN c_status[tx].resp)) \ keys

                        part_msg == {part \in PART: \A k \in all_keys: key_part[k] = part} \* set with ids to partitoin to message
                        part_abort == [part \in part_msg |-> (part_key[part] \intersect all_keys)]
                        set_msg == {Mk_msg("Abort",p,part,part_abort[part],msg.timestamp,msg.id):part \in part_msg}

                        new_inbox(msg_set) == [part \in (PART \ {p}) |->{m \in msg_set:m.id = part} \union inbox[part]] @@ [part \in {p}|->inbox[part]\{msg}]
                      IN 
                        /\ msg.type = "Prepare"
                        /\ ~(\A key \in keys: Check_key_write(msg.timestamp,msg.id,key))
                        /\ db' = [key \in keys |-> Append(db[key],[val|->msg.msg[key],timestamp|->my_time,state|->"ABORTED",tx |-> msg.id])] @@ db
                        /\ inbox' = new_inbox(set_msg)
                        /\ result' = [result EXCEPT ![tx] = result[tx] \union {[type|->"WRITE",ret|->"ABORT"]}]
                        /\ c_status' = [c_status EXCEPT ![tx] = [status|->"INACTIVE",time |-> START_TIMESTAMP,key_set |-> {},resp|-><<>>] @@ c_status[tx]]
                        /\ Update_time(p)
                        /\ UNCHANGED <<key_part,part_key>>

\* TODO: remove 
Commit_msg(p,msg) == LET
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
                        /\ Update_time(p)
                        /\ UNCHANGED <<key_part,part_key,c_status,result>>

\* TODO: remove 
Abort_msg(p,msg) == LET
                        update_entry(entry) == IF entry.state = "PREPARED" THEN
                                                    [state |-> "ABORTED",timestamp |-> msg.timestamp] @@ entry 
                                               ELSE entry
                        aux_db == [key \in msg.msg |-> [n \in 1..Len(db[key]) |-> update_entry(db[key][n])]]
                    IN
                    /\ msg.type = "Abort"
                    /\ \A key \in msg.msg:\E n \in 1..Len(db[key]): db[key][n].state = "PREPARED"
                    /\ db' = aux_db @@ db 
                    /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \ {msg}]
                    /\ Update_time(p)
                    /\ UNCHANGED <<key_part,part_key,c_status,result>>

\*------------------------------------------------------------------------
\* Message recive by coordinatoor

Recv_msg == \E p \in PART:\E msg \in inbox[p]:
                /\ msg.timestamp <= Get_time(p)
                /\(   Abort_msg(p,msg)
                   \/ Commit_msg(p,msg) 
                   \/ Write_abort(p,msg)
                   \/ Write_msg(p,msg)
                   \/ Read_msg(p,msg)
                   \/ Finish_read(p,msg))


Finish_write(tx) == LET
                        p == c_status[tx].part
                        keys == DOMAIN c_status[tx].resp
                        times == {c_status[tx].resp[key]: key \in keys}
                        t == CHOOSE t \in times: \A t1 \in times: t >= t1
                        parts_msg == {part \in PART: \E k \in keys: key_part[k] = part} \* set with ids to partitoin to message
                        set_msg(t_max) == {Mk_msg("Commit",p,part,keys \intersect part_key[part],t_max,tx):part \in parts_msg}
                    IN
                         /\ c_status[tx].status = "WRITE"
                         /\ c_status[tx].key_set = {}
                         /\ c_status' = [c_status EXCEPT ![tx] = [status|->"INACTIVE",time |-> START_TIMESTAMP,tx|-> NOVAL,key_set |-> {},resp|-> <<>>] @@ c_status[tx]]
                         /\ inbox' = Send_msg(set_msg(t))
                         /\ result' = [result EXCEPT ![tx] = result[tx] \union {[type|-> "WRITE",ret|->"OK"]}] 
                         /\ UNCHANGED <<db,key_part,part_key,time>>

Finish_op == \E tx \in TX_ID: Finish_write(tx) 


Next_part == (Finish_op \/ Recv_msg ) /\ UNCHANGED vars_snap

\* Snapshot model --------------------------------------------------------------

Init_snap == /\ snapshot = [t \in TX_ID |-> [k \in KEY |-> NOVAL]]
             /\ read_keys = [t \in TX_ID |-> {}]
             /\ write_keys = [t \in TX_ID |-> {}]
             /\ state = [t \in TX_ID |-> "START"]


Start(tx) == /\ state[tx] = "START"
             /\ \E rk \in SUBSET KEY:
                    \E wk \in SUBSET KEY:
                        /\ rk \union wk # {}
                        /\ read_keys' = [read_keys EXCEPT ![tx] = rk]
                        /\ write_keys' = [write_keys EXCEPT ![tx] = wk]
            /\ state' = [state EXCEPT ![tx] = "READ"]  
            /\ Start_tx(tx)
            /\ UNCHANGED <<snapshot,result>>

Start_read(tx) == /\ state[tx] = "READ"
                  /\ read_keys[tx] # {}
                  /\ state' = [state EXCEPT ![tx] = "WAIT_READ"]
                  /\ Read(read_keys[tx],tx)
                  /\ UNCHANGED <<snapshot,read_keys,write_keys,result>>

Start_read_empty(tx) == /\ state[tx] = "READ"
                        /\ read_keys[tx] = {}
                        /\ state' = [state EXCEPT ![tx] = "WRITE"]
                        /\ UNCHANGED <<snapshot,read_keys,inbox,write_keys,result,c_status,time>>

Read_snap(tx) == /\ state[tx] = "WAIT_READ"
                 /\ \E ret \in result[tx]: (ret.type = "READ"
                    /\ snapshot' = [snapshot EXCEPT ![tx] =  ret.ret @@ snapshot[tx]]
                    /\ result' = [result EXCEPT ![tx] = result[tx] \ {ret}])
                 /\ state' = [state EXCEPT ![tx] = IF write_keys[tx] # {} THEN "WRITE" ELSE "DONE"]
                 /\ UNCHANGED <<read_keys,write_keys,inbox,c_status,time>>

Start_write(tx) == /\ state[tx] = "WRITE"
                   /\ Write([key \in write_keys[tx] |-> tx],tx)
                   /\ state' = [state EXCEPT ![tx] = "WAIT_WRITE"]
                   /\ UNCHANGED <<snapshot,read_keys,write_keys,result>>

Write_snap_success(tx) == /\ snapshot' = [snapshot EXCEPT ![tx] = [key \in write_keys[tx] |-> tx]]
                     /\ state' = [state EXCEPT ![tx] = "DONE"] 
                     /\ UNCHANGED <<read_keys,write_keys,inbox,c_status,time>> 

Write_snap_abort(tx) == /\ state' = [state EXCEPT ![tx] = "DONE"]
                   /\ UNCHANGED <<read_keys,write_keys,snapshot,inbox,c_status,time>>

Write_snap(tx) == /\ state[tx] = "WAIT_WRITE"
             /\ \E ret \in result[tx]: ret.type = "WRITE"
             /\ result' = [result EXCEPT ![tx] = result[tx]\ {ret}]
             /\ IF ret.ret = "OK" THEN
                    Write_snap_abort(tx)
                ELSE 
                    Write_snap_success(tx)

Terminating == \A tx \in TX_ID: state[tx] = "DONE" /\ UNCHANGED vars

  
Next_snap == ((\E tx \in TX_ID: Start(tx) \/ Start_read(tx) \/ Start_read_empty(tx) \/ Read_snap(tx) \/ Start_write(tx) \/ Write_snap(tx)) \/ Terminating) /\ UNCHANGED vars_part

\*---------------------------------------------------------------------------------

Init == Init_part /\ Init_snap /\ result = [tx \in TX_ID |-> {}]

Next == Next_snap \/ Next_part

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

All_finish == <> (\A tx \in TX_ID:state[tx] = "DONE")

================================







