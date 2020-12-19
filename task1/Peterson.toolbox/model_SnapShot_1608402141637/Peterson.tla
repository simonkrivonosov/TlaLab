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

(***************************************************************************)
(* Adds fairness guarantees to our basic specification.  This allows us to *)
(* show liveness (WillEventuallyEnterCritical) by postulating that the     *)
(* overall state always eventually changes and that both processes will    *)
(* eventually request to access the shared resource.                       *)
(***************************************************************************)
SpecWithFairness == Spec /\ WF_vars(Next) /\ \A p \in {0, 1} : WF_vars(ProcessWantAccess(p))

(***************************************************************************)
(* Now we move on to the invariants we wish to hold! (And one which we     *)
(* don't).  Note that there is one property of Peterson's algorithm which  *)
(* we do not show here; in fact as far as I'm aware it is not possible to  *)
(* show with TLA+ without some invasive contortions.  Bounded waiting,     *)
(* that is that a process will never wait more than a fixed N steps to     *)
(* enter its critical section after requesting to do so, is hard to show   *)
(* in TLA+ because TLA+ doesn't offer tools to reason about the particular *)
(* execution trace of a model over time.                                   *)
(***************************************************************************)

(***************************************************************************)
(* This is the basic mutual exclusion property.  Only one process at a     *)
(* time should access the shared resource, i.e.  enter its own critical    *)
(* section.  This is the central purpose of Peterson's algorithm.          *)
(***************************************************************************)
MutualExclusion == ~(processState[0] = "critical" /\ processState[1] = "critical")

THEOREM Spec => []MutualExclusion

(***************************************************************************)
(* This is a basic liveness requirement that corresponds to what is called *)
(* "Progress" in the Wikipedia article.  Both processes should eventually  *)
(* be able to enter their critical sections.                               *)
(***************************************************************************)
WillEventuallyEnterCritical == <>(processState[0] = "critical") /\ <>(processState[1] = "critical")

THEOREM SpecWithFairness => WillEventuallyEnterCritical

(***************************************************************************)
(* THIS INVARIANT DOES NOT HOLD AND SHOULD NOT HOLD! It's merely           *)
(* instructive of something a reader may intuitively believe about this    *)
(* algorithm that turns out to be false.                                   *)
(*                                                                         *)
(* See the note in ProcessEnterCritical.                                   *)
(***************************************************************************)
CanOnlyBeCriticalIfTurn == \A p \in {0, 1} : processState[p] = "critical" => turn = p

(***************************************************************************)
(* Finally we note simply that our variables should always stay within the *)
(* bounds we enumerated earlier.                                           *)
(***************************************************************************)
THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Sat Dec 19 21:22:11 MSK 2020 by simon
\* Last modified Mon Jul 29 13:36:49 EDT 2019 by changlin
\* Created Wed Jul 24 18:56:50 EDT 2019 by changlin
