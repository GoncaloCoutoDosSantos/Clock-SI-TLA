---- MODULE MC ----
EXTENDS Clock_SI, TLC

CONSTANTS k1,k2,k3

CONSTANTS p1,p2

CONSTANTS  t1,t2,t3

C_KEY == {k1,k2,k3}

C_PART == {p1,p2}

C_TX_ID == {t1,t2,t3}

C_KEY_PART == (k1 :> p1 @@ k2 :> p2 @@ k3 :> p2)

C_PART_KEY == [p \in C_PART |-> {k \in KEY: C_KEY_PART[k] = p}] 

================================
