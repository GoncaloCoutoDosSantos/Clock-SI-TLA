---- MODULE MC ----
EXTENDS Clock_SI, TLC

CONSTANTS k1,k2,k3

CONSTANTS p1,p2,p3

CONSTANTS  t1,t2

C_KEY == {k1,k2,k3}

C_PART == {p1,p2,p3}

C_TX_ID == {t1,t2}

C_VALUE == TX_ID \union {NOVAL}

C_KEY_PART == (k1 :> p1 @@ k2 :> p2 @@ k3 :> p3)

C_PART_KEY == [p \in C_PART |-> {k \in KEY: C_KEY_PART[k] = p}] 

C_TIME == 3

C_SYMMETRIC == Permutations(C_KEY) \union 
               Permutations(C_PART) \union
               Permutations(C_TX_ID) 
================================
