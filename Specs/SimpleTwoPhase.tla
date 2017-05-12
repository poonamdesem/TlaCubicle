--------------------------- MODULE SimpleTwoPhase ---------------------------
CONSTANT RM
VARIABLES Coordinator,rmState

Cmessage == {"init","Ccommit","Cabort"}
RmMessage == {"working","proposeCommit","proposeAbort","committed","aborted"}

TypeOK == /\ rmState \in [RM -> RmMessage]
          /\ Coordinator \in Cmessage

Init == /\ rmState  = [rm  \in RM |-> "working"] 
        /\ Coordinator = "init"
          
        
Ccommit == 
  /\ \A rm \in RM:rmState[rm] \in {"proposeCommit"}
  /\ Coordinator = "init"
  /\ Coordinator' = "Ccommit"
  /\ rmState' =  rmState
  

Cabort == /\ \E rm \in RM: rmState[rm] \in {"proposeAbort"}
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
        /\ rmState[rm] # "committed"
        /\ rmState'  = [rmState EXCEPT ![rm]="committed"] 
        /\ Coordinator' = Coordinator
        
        
Abort(rm) == 
        /\ Coordinator = "Cabort"
        /\ rmState[rm] # "aborted"
        /\ rmState'  = [rmState EXCEPT ![rm]="aborted"] 
        /\ Coordinator' = Coordinator
             
Final ==  \/ ((\A rm \in RM : rmState[rm] = "aborted") /\ UNCHANGED <<rmState, Coordinator>>)
          \/ ((\A rm \in RM : rmState[rm] = "committed") /\ UNCHANGED <<rmState, Coordinator>> )      
        

Next ==  
  \/ Ccommit \/  Cabort \/ Final
  \/ \E rm \in RM: DecisionCommit(rm) \/ DecisionAbort(rm) \/ Commit(rm) \/ Abort(rm)
           
           

Spec ==  Init /\ [] [Next]_<<rmState,Coordinator>>

Consistent ==
    \A rm1,rm2 \in RM: ~ /\ rmState[rm1]="aborted"
                         /\ rmState [rm2] = "commited"


Inv == ~ (\E x,y \in RM : x # y /\ rmState[x] = "aborted" /\ rmState[y] = "proposeAbort") 
\*Terminates == <> \/ (\A rm \in RM : rmState[rm] = "aborted")
\*                 \/ (\A rm \in RM : rmState[rm] = "committed")

CCommitAbort == Coordinator = "Ccommit" => (\A x \in RM : rmState[x] # "aborted")
CAbortCommit == Coordinator = "Cabort" => (\A x \in RM : rmState[x] # "committed")

\* CorA == <>[][(Coordinator = "Cabort" \/ Coordinator = "Ccommit")]_<<Coordinator,rmState>>
CorA == <>[][(Coordinator # "init")]_<<Coordinator,rmState>>

NonTerm == ~ <>[][Final]_<<Coordinator,rmState>>

=============================================================================
\* Modification History
\* Last modified Fri May 12 18:15:27 CEST 2017 by marty
\* Last modified Wed Mar 29 10:07:24 CEST 2017 by poonam
\* Created Tue Mar 28 17:42:30 CEST 2017 by poonam
