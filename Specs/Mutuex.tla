------------------------------- MODULE Mutuex -------------------------------
CONSTANT PROC \* Set of Process
VARIABLES Want,Crit,Turn

TypeOK == 
         /\ Want \in [PROC -> BOOLEAN] 
         /\ Crit \in [PROC -> BOOLEAN]
         /\ Turn \in PROC

         
       
Init == /\ Want  = [i  \in PROC |-> FALSE] 
        /\ Crit  = [i  \in PROC |-> FALSE] 
        /\ Turn \in PROC 

req(i) == 
        /\ Want[i] = FALSE
        /\ Want' = [Want EXCEPT ![i]=TRUE]
        /\ Crit' = Crit 
        /\ Turn' = Turn
        
enter(i) == 
        /\ Want[i] = TRUE
        /\ Crit[i] = FALSE
        /\ Turn = i
        /\ Crit' = [Crit EXCEPT ![i]=TRUE]
        /\ Want' = Want 
        /\ Turn' = Turn
        
exit(i) == 
        /\ Crit[i] = TRUE
        /\ Crit' = [Crit EXCEPT ![i]=FALSE]
        /\ Want' = [Want EXCEPT ![i]=FALSE] 
        /\ Turn' \in PROC

        
Next ==   \/ \E i \in PROC: 
		\/req(i)
		\/ enter(i)
		\/ exit(i) 

Spec == Init /\ [][Next]_<<Want,Crit,Turn>>
    
        
(*Safety ==  ~ \E p1,p2 \in PROC: p1 # p2 /\ Crit[p1]=TRUE /\ Crit[p2] = TRUE  *)
Safety ==   \A p1,p2 \in PROC:  ~ (p1 # p2 
				/\ Crit[p1]="TRUE"
				/\ Crit[p2] = "TRUE" )     
   
=============================================================================
\* Modification History
\* Last modified Mon May 15 12:50:23 CEST 2017 by poonam
\* Created Mon Mar 27 13:06:51 CEST 2017 by poonam
