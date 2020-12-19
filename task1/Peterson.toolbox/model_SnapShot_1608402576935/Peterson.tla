------------------------------ MODULE Peterson ------------------------------


EXTENDS Integers

VARIABLES 
    turn, 
    processState, 
    want 

vars == <<turn, processState, want>> 

TypeOK ==
    /\ \A p \in {0, 1} : want[p] \in {TRUE, FALSE}
    /\ turn \in {0, 1}
    /\ \A p \in {0, 1} : processState[p] \in {"none", "wantAccess", "waiting", "critical"}

Init ==
    /\ want = [i \in {0, 1} |-> FALSE]
    /\ turn \in {0, 1}
    /\ processState = [i \in {0, 1} |-> "none"]
    
   
ProcessWantAccess(p) ==
    /\ processState[p] = "none"
    /\ want' = [want EXCEPT ![p] = TRUE]
    /\ processState' = [processState EXCEPT ![p] = "wantAccess"]
    /\ UNCHANGED <<turn>>

 
ProcessBeginWaiting(p) ==
    /\ processState[p] = "wantAccess"
    /\ turn' = 1 - p
    /\ processState' = [processState EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<want>>
    

ProcessEnterCritical(p) ==
    /\ processState[p] = "waiting"
    /\ (want[(1 - p)] = FALSE \/ turn = p)
    /\ processState' = [processState EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<want, turn>>


ProcessExitCritical(p) ==
    /\ processState[p] = "critical"
    /\ processState' = [processState EXCEPT ![p] = "none"]
    /\ want' = [want EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn>>


Next ==
    \E p \in {0, 1} :
        \/ ProcessWantAccess(p)
        \/ ProcessBeginWaiting(p)
        \/ ProcessEnterCritical(p)
        \/ ProcessExitCritical(p)
    

Spec == Init /\ [][Next]_vars 


SpecWithFairness == Spec /\ WF_vars(Next) /\ \A p \in {0, 1} : WF_vars(ProcessWantAccess(p))


MutualExclusion == ~(processState[0] = "critical" /\ processState[1] = "critical")

THEOREM Spec => []MutualExclusion


WillEventuallyEnterCritical == <>(processState[0] = "wantAccess") /\ <>(processState[1] = "wantAccess")

THEOREM SpecWithFairness => WillEventuallyEnterCritical


THEOREM Spec => []TypeOK

=============================================================================
