-------------------- MODULE LeaderConsensusSpecification --------------------

EXTENDS FiniteSets,
        Integers,
        Sequences,
        SequenceOps,
        TLAPS,
        TLC

----------------------------------------------------------------------------

CONSTANT NumProcessors

ASSUME NumProcessorAsm == NumProcessors \in Nat\{0}

ProcessorSet == 1..NumProcessors

----------------------------------------------------------------------------

CONSTANT NumWaves

ASSUME NumWaveAsm == NumWaves \in Nat\{0}

WaveSet == 1..NumWaves

----------------------------------------------------------------------------

(* For every process p and wave w, commitWithRef stores  the sequence of  *)
(* waves that w will commit if decided by process p.                      *) 

VARIABLES commitWithRef

CommitWithRefType = commitWithRef \in [ProcessorSet -> [WaveSet -> Seq(WaveSet)]]

------------------------------

(* For every process p, decidedWave stores the last decided wave by p.    *)

VARIABLES decidedWave

DecidedWaveType = decidedWave \in [ProcessorSet -> WaveSet \cup {0}]

------------------------------

(* For every process p and wave w leaderReachablity stores information   *)
(* about existence of leader vertex of w in the DAG of p, along with the *)
(* set of waves whose leader vertices are reachable from leader vertex   *)
(* of w.                                                                 *)

VARIABLES leaderReachablity

LeaderReachabilityType = leaderReachablity \in [ProcessorSet -> [WaveSet -> [exists : BOOLEAN, edges : SUBSET(WaveSet)]]]

------------------------------

(* For every process p, leaderSeq stores the sequence of waves (in the   *)
(* increasing order) committed by the last and the previous last decided *) 
(* wave.                                                                 *)

VARIABLES leaderSeq

LeaderSeqType = leaderSeq \in [ProcessorSet -> [current : Seq(WaveSet), last : Seq(WaveSet)]]

------------------------------

StateType == 
          /\ CommitWithRefType
          /\ DecidedWaveType
          /\ LeaderReachablityType
          /\ LeaderSeqType

----------------------------------------------------------------------------

Init == /\ commitWithRef = [p \in ProcessorSet |-> [w \in WaveSet |-> <<>>]]
        /\ decidedWave = [p \in ProcessorSet |-> 0]
        /\ leaderReachablity = [p \in ProcessorSet |-> [w \in WaveSet |->[exists |-> FALSE, edges |-> {}]]]
        /\ leaderSeq = [p \in ProcessorSet |-> [current |-> <<>>, last |-> <<>>]]

----------------------------------------------------------------------------
        
max(E) == IF E # {} /\ Cardinality(E) \in Nat THEN CHOOSE x \in E : \A y \in E : y <= x ELSE "Error"   
  
UpdateWaveTn(p, w, E) ==   /\ leaderReachablity[p][w].exists = FALSE
                           /\ \A x \in E : leaderReachablity[p][x].exists = TRUE
                           /\ \A x \in E : x < w
                           /\ \A q \in ProcessorSet : leaderReachablity[q][w].exists = TRUE => leaderReachablity[q][w].edges = E
                           /\ \A q \in ProcessorSet : decidedWave[q] # 0 /\ decidedWave[q] < w => decidedWave[q] \in E
                           /\ commitWithRef' = [commitWithRef EXCEPT ![p][w] = IF E = {} THEN <<w>> ELSE Append(commitWithRef[p][max(E)], w)]
                           /\ leaderReachablity' = [leaderReachablity EXCEPT ![p][w] = [exists |-> TRUE, edges |-> E]]
                           /\ UNCHANGED <<decidedWave, leaderSeq>>

UpdateDecidedWaveTn(p, w) ==   /\ leaderReachablity[p][w].exists = TRUE
                               /\ w >= decidedWave[p]
                               /\ \A x \in WaveSet : x > w => leaderReachablity[p][x].exists = FALSE 
                               /\ \A q \in ProcessorSet, x \in WaveSet : x > w /\ leaderReachablity[q][x].exists = TRUE => w \in leaderReachablity[q][x].edges
                               /\ decidedWave' = [decidedWave EXCEPT ![p] = w]
                               /\ leaderSeq' = [leaderSeq EXCEPT ![p] = [current |-> commitWithRef[p][w], last |-> leaderSeq[p].current]]
                               /\ UNCHANGED <<commitWithRef, leaderReachablity>>

----------------------------------------------------------------------------
                               
Next == \E p \in ProcessorSet, w \in WaveSet, E \in SUBSET(WaveSet) : UpdateWaveTn(p, w, E) \/ UpdateDecidedWaveTn(p, w)

----------------------------------------------------------------------------

vars == <<commitWithRef, decidedWave, leaderReachablity, leaderSeq>>

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

LeaderConsensusMonotonicity == \A p \in ProcessorSet : IsPrefix(leaderSeq[p].last, leaderSeq[p].current)

LeaderConsensusConsistancy == \A p, q \in ProcessorSet : decidedWave[p] <= decidedWave[q] => IsPrefix(leaderSeq[p].current, leaderSeq[q].current)

Contains(w, S) == \E i \in 1..Len(S) : S[i] = w

----------------------------------------------------------------------------

Invariant1 == \A p \in ProcessorSet : decidedWave[p] # 0 => leaderReachablity[p][decidedWave[p]].exists = TRUE

Invariant2 == \A p \in ProcessorSet : leaderSeq[p].current = IF decidedWave[p] = 0 THEN <<>> ELSE commitWithRef[p][decidedWave[p]]

Invariant3 == \A p \in ProcessorSet, w \in WaveSet: \A x \in leaderReachablity[p][w].edges : leaderReachablity[p][x].exists = TRUE

Invariant4 == \A p \in ProcessorSet, w, x \in WaveSet : Contains(w, commitWithRef[p][x]) => leaderReachablity[p][w].exists = TRUE

Invariant5 == \A p \in ProcessorSet, w, x \in WaveSet : Contains(w, commitWithRef[p][x]) => IsPrefix(commitWithRef[p][w], commitWithRef[p][x])

Invariant6 == \A p \in ProcessorSet, w \in WaveSet: leaderReachablity[p][w].exists = TRUE => commitWithRef[p][w] = IF leaderReachablity[p][w].edges = {} THEN <<w>> ELSE Append(commitWithRef[p][max(leaderReachablity[p][w].edges)], w) 

Invariant7 == \A p, q \in ProcessorSet, w \in WaveSet : leaderReachablity[p][w].exists = leaderReachablity[q][w].exists => commitWithRef[p][w] = commitWithRef[q][w]

Invariant8 == \A p \in ProcessorSet, w \in WaveSet : (\A y \in WaveSet : y > w /\ leaderReachablity[p][y].exists => w \in leaderReachablity[p][y].edges) => (\A y \in WaveSet : y >= w /\ leaderReachablity[p][y].exists => Contains(w, commitWithRef[p][y])) 

Invariant9 == \A p, q \in ProcessorSet, w \in WaveSet : decidedWave[p] # 0 /\ w >= decidedWave[p] /\ leaderReachablity[q][w].exists = TRUE => Contains(decidedWave[p], commitWithRef[q][w])

Invariant10 == \A p, q \in ProcessorSet, w \in WaveSet : leaderReachablity[p][w].exists = TRUE /\ w >= decidedWave[q] /\ decidedWave[q] # 0 => IsPrefix(commitWithRef[q][decidedWave[q]], commitWithRef[p][w]) 

=============================================================================
