--------------------------- MODULE SimpleTwoPhase ---------------------------
CONSTANT RM
VARIABLES Coordinator,rmState


TypeOK == /\ rmState \in [RM -> {"working","proposeCommit","proposeAbort","committed","aborted"}] 
          /\ Coordinator \in {"init","Ccommit","Cabort"}

Init == /\ rmState  = [rm  \in RM |-> "working"] 
        /\ Coordinator = "init"
          
        
Ccommit == 
  /\ \A rm \in RM:rmState[rm] \in {"proposeCommit"}
  /\ Coordinator = "init"
  /\ Coordinator' = "Ccommit"
  /\ rmState' =  rmState
  

Cabort == /\ \E rm \in RM:rmState[rm] \in {"proposeAbort"}
          /\ Coordinator = "init"
          /\ Coordinator' = "Cabort"
          /\ rmState' =  rmState
          
(*Decide(rm) == 
        /\ rmState[rm] = "working"
        /\ \E v \in {"proposeCommit","proposeAbort"} : 
              rmState'  = [rmState EXCEPT ![rm]=v] 
        /\ Coordinator' = Coordinator *)
DecisionCommit(rm) == 
        /\ rmState[rm] = "working"
        /\ rmState'  = [rmState EXCEPT ![rm]="proposeCommit"] 
        /\ Coordinator' = Coordinator
        
DecisionAbort(rm) == 
        /\ rmState[rm] = "working"
        /\ rmState'  = [rmState EXCEPT ![rm]="proposeAbort"] 
        /\ Coordinator' = Coordinator        
        
        
Commit(rm) == 
        /\ Coordinator = "Ccommit"
        /\ rmState'  = [rmState EXCEPT ![rm]="committed"] 
        /\ Coordinator' = Coordinator
        
        
Abort(rm) == 
        /\ Coordinator = "Cabort"
        /\ rmState'  = [rmState EXCEPT ![rm]="aborted"] 
        /\ Coordinator' = Coordinator
             
        

Next ==  
  \/ Ccommit \/  Cabort
  \/ \E rm \in RM: DecisionCommit(rm) \/ DecisionAbort(rm) \/ Commit(rm) \/ Abort(rm)
           
           

Spec ==  Init /\ [] [Next]_<<rmState,Coordinator>>

Consistent ==
    \A rm1,rm2 \in RM: ~ /\ rmState[rm1]="aborted"
                         /\ rmState [rm2] = "commited"


=============================================================================
\* Modification History
\* Last modified Wed Mar 29 10:07:24 CEST 2017 by poonam
\* Created Tue Mar 28 17:42:30 CEST 2017 by poonam
