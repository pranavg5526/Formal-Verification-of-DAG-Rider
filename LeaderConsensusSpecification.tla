-------------------- MODULE LeaderConsensusSpecification --------------------

EXTENDS FiniteSets,
        Integers,
        Sequences,
        SequenceOps,
        TLAPS,
        TLC

----------------------------------------------------------------------------
(*-----------------------------CONSTANS----------------------------------*)

(* NumProcessors is the number of participating processes in the         *)
(* protocol, we assume this is non zero. We number processes 1 to        *)
(* NumProcessors and define ProcessorSet as the set of participating     *)
(* processes.                                                            *)

CONSTANT NumProcessors

ASSUME NumProcessorAsm == NumProcessors \in Nat\{0}

ProcessorSet == 1..NumProcessors

------------------------------

(* NumWaves is the number of waves after which protocol will stop, we    *)
(* assume this is non zero. We number waves 1 to NumWaves and define     *)
(* WaveSet as the set of participating processes.                        *)

CONSTANT NumWaves

ASSUME NumWaveAsm == NumWaves \in Nat\{0}

WaveSet == 1..NumWaves

----------------------------------------------------------------------------
(*------------------------STATE-VARIABLSE--------------------------------*)

(* For every process p and wave w, commitWithRef stores  the sequence of *)
(* waves that w will commit if decided by process p.                     *) 

VARIABLES commitWithRef

CommitWithRefType == 
   commitWithRef \in [ProcessorSet -> [WaveSet -> Seq(WaveSet)]]

InitCommitWithRef == 
   commitWithRef = [p \in ProcessorSet |-> [w \in WaveSet |-> <<>>]]

------------------------------

(* For every process p, decidedWave stores the last decided wave by p.   *)

VARIABLES decidedWave

DecidedWaveType == 
   decidedWave \in [ProcessorSet -> WaveSet \cup {0}]

InitDecidedWave == 
   decidedWave = [p \in ProcessorSet |-> 0]

------------------------------

(* For every process p and wave w leaderReachablity stores information   *)
(* about existence of leader vertex of w in the DAG of p, along with the *)
(* set of waves whose leader vertices are reachable from leader vertex   *)
(* of w.                                                                 *)

VARIABLES leaderReachablity

LeaderReachabilityType == 
   leaderReachablity \in [ProcessorSet -> [WaveSet -> [exists : BOOLEAN, edges : SUBSET(WaveSet)]]]

InitLeaderReachability == 
   leaderReachablity = [p \in ProcessorSet |-> [w \in WaveSet |->[exists |-> FALSE, edges |-> {}]]]

------------------------------

(* For every process p, leaderSeq stores the sequence of waves (in the   *)
(* increasing order) committed by the last and the previous last decided *) 
(* wave.                                                                 *)

VARIABLES leaderSeq

LeaderSeqType == 
   leaderSeq \in [ProcessorSet -> [current : Seq(WaveSet), last : Seq(WaveSet)]]

InitLeaderSeq == 
   leaderSeq = [p \in ProcessorSet |-> [current |-> <<>>, last |-> <<>>]]

----------------------------------------------------------------------------
(*------------------------STATE-TRANSITIONS------------------------------*)
 
(* Every process p, upon adding a leader vertex of a wave w updates the  *)
(* leaderReachablity state with the transition UpdateWaveTn(p, w, E).    *)    
(* Here E is the set of waves whose leader vertex is reachable from the  *)
(* leader vertex of w. The transition is restricted to 5 pre conditions  *)
(* derived from DAG-construction and consensus protocol, below, we       *)
(* informally describe underlying property behind each one of these      *)
(* conditions:                                                           *)
(*  (1) For any process p and wave w there is a unique leader vertex of  *)
(*      w, which is added atmost once to the DAG of p.                   *)
(*  (2) Vertices are added only after their causal histories are added.  *)
(*  (3) Vertices have paths only to vertices in the lower rounds.        *)   
(*  (4) Causal histories of a added vertex in the DAG of two proceese    *)
(*      is same.                                                         *)
(*  (5) If a wave w is decided by some process p then in every process   *)
(*      q whose current wave of construction is higher than w, leader    *)
(*      vertex of w exists and is reachable from all the vertices in the *)
(*      subsequent waves of q's DAG. This is derived by qouram           *)
(*      intersection argument applied on some of the properties of       *)
(*      DAG-construction and consensus protocol.                         *)
(* On taking UpdateWaveTn(p, w, E), the state variable leaderReachablity *)
(* is updated with its value for process p and wave w. Addtionally we    *)
(* update commitWithRef variable for wave w of process p, for this we    *)
(* define max of a set. THe remaining two variables, decidedWave and     *)
(* leaderSeq remain unchanged during this execution.                     *)
                                                                        

max(E) == 
   IF E # {} /\ Cardinality(E) \in Nat 
   THEN CHOOSE x \in E : \A y \in E : y <= x 
   ELSE "Error"

UpdateWaveTn(p, w, E) ==   
   /\ leaderReachablity[p][w].exists = FALSE
   /\ \A x \in E : leaderReachablity[p][x].exists = TRUE
   /\ \A x \in E : x < w
   /\ \A q \in ProcessorSet: 
      leaderReachablity[q][w].exists = TRUE => leaderReachablity[q][w].edges = E
   /\ \A q \in ProcessorSet: 
      decidedWave[q] # 0 /\ decidedWave[q] < w => decidedWave[q] \in E
   /\ commitWithRef' = [commitWithRef EXCEPT ![p][w] = IF E = {} THEN <<w>> ELSE Append(commitWithRef[p][max(E)], w)]
   /\ leaderReachablity' = [leaderReachablity EXCEPT ![p][w] = [exists |-> TRUE, edges |-> E]]
   /\ UNCHANGED <<decidedWave, leaderSeq>>

------------------------------

(* Every process p, upon deciding new wave updates decidedWave with      *)
(* the transition UpdateDecidedWaveTn(p, w). The transition is           *)
(* restricted to 5 pre conditions derived from DAG-construction and      *) 
(* consensus protocol, below, we informally describe underlying          *)
(* property behind each one of these conditions:                         *)                           
(*  (1) A wave is decided by a process only if the leader vertex of      *)
(*      the wave is in the DAG of the process.                           *)
(*  (2) The decided wave is always less than or equal to current wave    *)
(*      of DAG construction.                                             *)
(*  (3) A wave is decided before entering the next wave in the DAG       *)
(*      construction.                                                    *)
(*  (4) If a wave w is decided by some process p then in every process   *)
(*      q whose current wave of construction is higher than w, leader    *)
(*      vertex of w exists and is reachable from all the vertices in the *)
(*      subsequent waves of q's DAG. This is derived by qouram           *)
(*      intersection argument applied on some of the properties of       *)
(*      DAG-construction and consensus protocol.                         *)
(* On taking UpdateDecidedWaveTn(p, w), the state variable               *)
(* decidedRefWave is updated with its value for process p. Addtionally   *)
(* we update leaderSeq variable by referring to the value of             *)
(* commitWithRef variable for process p and wave w. The remaining two    *)
(* state variables commitWithRef and leaderReachablity remain unchanged  *)
(* during this execution.                                                *)


UpdateDecidedWaveTn(p, w) ==
   /\ leaderReachablity[p][w].exists = TRUE
   /\ w >= decidedWave[p]
   /\ \A x \in WaveSet : x > w => leaderReachablity[p][x].exists = FALSE 
   /\ \A q \in ProcessorSet, x \in WaveSet:  
      x > w  /\ leaderReachablity[q][x].exists = TRUE => w \in leaderReachablity[q][x].edges
   /\ decidedWave' = [decidedWave EXCEPT ![p] = w]
   /\ leaderSeq' = [leaderSeq EXCEPT ![p] = [current |-> commitWithRef[p][w], last |-> leaderSeq[p].current]]
   /\ UNCHANGED <<commitWithRef, leaderReachablity>>

----------------------------------------------------------------------------
(*--------------------------COMPLETE-SPEC--------------------------------*)

(* To complete the transition system specification we define Init, Next, *)
(* vars, Spec. Typical TLA+ macro names for the initial state, possible  *)
(* actions leading to the next state, the variables, and the system      *)
(* specification, respectively.                                          *)

StateType == 
   /\ CommitWithRefType
   /\ DecidedWaveType
   /\ LeaderReachabilityType
   /\ LeaderSeqType

Init == 
   /\ InitCommitWithRef
   /\ InitDecidedWave
   /\ InitLeaderReachability
   /\ InitLeaderSeq
        
Next == 
   \E p \in ProcessorSet, w \in WaveSet, E \in SUBSET(WaveSet): 
      UpdateWaveTn(p, w, E) \/ UpdateDecidedWaveTn(p, w)

vars == <<commitWithRef, decidedWave, leaderReachablity, leaderSeq>>

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(*-------------------------SAFETY-INVARIANTS-----------------------------*)

(* Monotonicity states that the commitment of waves                      *)
(* happen monotonically with respect to the decided waves, that is the   *)
(* order in which waves are committed so far wont be altered in future   *)
(* with a new decided wave.                                              *)

Monotonicity == 
   \A p \in ProcessorSet: 
      IsPrefix(leaderSeq[p].last, leaderSeq[p].current)

------------------------------

(* Assuming every process keeps on deciding new waves,                   *)
(* Consistency states that eventually all the processes                  *)
(* commit the same waves and in the same order.                          *)

Consistency == 
   \A p, q \in ProcessorSet: 
      decidedWave[p] <= decidedWave[q] => IsPrefix(leaderSeq[p].current, leaderSeq[q].current)

------------------------------

Safety == Spec => [](Monotonicity /\ Consistency)

=============================================================================