------------------------ MODULE LeaderConsensus_Spec ------------------------
EXTENDS Integers, TLAPS, TLC, Sequences, FiniteSets, SequenceOps

CONSTANTS NumProcessors,
          NumWaves

ProcessorSet == 1..NumProcessors
WaveSet == 1..NumWaves
          
ASSUME NumProcessorAsm == NumProcessors \in Nat\{0}
ASSUME NumWaveAsm == NumWaves \in Nat\{0}

VARIABLES waveDAG, decidedWave, leaderSeq, commitWithRef

TypeOK == /\ waveDAG \in [ProcessorSet -> [WaveSet -> [exists : BOOLEAN, edges : SUBSET(WaveSet)]]]
          /\ decidedWave \in [ProcessorSet -> WaveSet \cup {0}]
          /\ leaderSeq \in [ProcessorSet -> [current : Seq(WaveSet), last : Seq(WaveSet)]]
          /\ commitWithRef \in [ProcessorSet -> [WaveSet -> Seq(WaveSet)]]

Init == /\ waveDAG = [p \in ProcessorSet |-> [w \in WaveSet |->[exists |-> FALSE, edges |-> {}]]]
        /\ decidedWave = [p \in ProcessorSet |-> 0]
        /\ leaderSeq = [p \in ProcessorSet |-> [current |-> <<>>, last |-> <<>>]]
        /\ commitWithRef = [p \in ProcessorSet |-> [w \in WaveSet |-> <<>>]]
        
max(E) == IF E # {} /\ Cardinality(E) \in Nat THEN CHOOSE x \in E : \A y \in E : y <= x ELSE "Error"   
  
update_waveDAG(p, w, E) == /\ waveDAG[p][w].exists = FALSE
                           /\ \A x \in E : waveDAG[p][x].exists = TRUE
                           /\ \A x \in E : x < w
                           /\ \A q \in ProcessorSet : waveDAG[q][w].exists = TRUE => waveDAG[q][w].edges = E
                           /\ \A q \in ProcessorSet : decidedWave[q] # 0 /\ decidedWave[q] < w => decidedWave[q] \in E
                           /\ waveDAG' = [waveDAG EXCEPT ![p][w] = [exists |-> TRUE, edges |-> E]]
                           /\ commitWithRef' = [commitWithRef EXCEPT ![p][w] = IF E = {} THEN <<w>> ELSE Append(commitWithRef[p][max(E)], w)]
                           /\ UNCHANGED <<decidedWave, leaderSeq>>

update_decidedWave(p, w) ==    /\ waveDAG[p][w].exists = TRUE
                               /\ w >= decidedWave[p]
                               /\ \A x \in WaveSet : x > w => waveDAG[p][x].exists = FALSE 
                               /\ \A q \in ProcessorSet, x \in WaveSet : x > w /\ waveDAG[q][x].exists = TRUE => w \in waveDAG[q][x].edges
                               /\ decidedWave' = [decidedWave EXCEPT ![p] = w]
                               /\ leaderSeq' = [leaderSeq EXCEPT ![p] = [current |-> commitWithRef[p][w] ,last |-> leaderSeq[p].current]]
                               /\ UNCHANGED <<waveDAG, commitWithRef>>
                               
Next == \E p \in ProcessorSet, w \in WaveSet, E \in SUBSET(WaveSet) : update_waveDAG(p, w, E) \/ update_decidedWave(p, w)

vars == <<waveDAG, decidedWave, leaderSeq, commitWithRef>>

Spec == Init /\ [][Next]_vars


ChainMonotonicity == \A p \in ProcessorSet : IsPrefix(leaderSeq[p].last, leaderSeq[p].current)

ChainConsistancy == \A p,q \in ProcessorSet : decidedWave[p] <= decidedWave[q] => IsPrefix(leaderSeq[p].current, leaderSeq[q].current)

Contains(w, S) == \E i \in 1..Len(S) : S[i]=w

Invariant1 == \A p \in ProcessorSet : decidedWave[p] # 0 => waveDAG[p][decidedWave[p]].exists = TRUE
Invariant2 == \A p \in ProcessorSet : leaderSeq[p].current = IF decidedWave[p] = 0 THEN <<>> ELSE commitWithRef[p][decidedWave[p]]
Invariant3 == \A p \in ProcessorSet, w \in WaveSet: \A x \in waveDAG[p][w].edges : waveDAG[p][x].exists = TRUE
Invariant4 == \A p \in ProcessorSet, w,x \in WaveSet : Contains(w, commitWithRef[p][x]) => waveDAG[p][w].exists = TRUE
Invariant5 == \A p \in ProcessorSet, w,x \in WaveSet : Contains(w, commitWithRef[p][x]) => IsPrefix(commitWithRef[p][w], commitWithRef[p][x])
Invariant6 == \A p \in ProcessorSet, w \in WaveSet: waveDAG[p][w].exists = TRUE => commitWithRef[p][w] = IF waveDAG[p][w].edges = {} THEN <<w>> ELSE Append(commitWithRef[p][max(waveDAG[p][w].edges)], w) 
Invariant7 == \A p, q \in ProcessorSet, w \in WaveSet : waveDAG[p][w].exists = waveDAG[q][w].exists => commitWithRef[p][w] = commitWithRef[q][w]
Invariant8 == \A p \in ProcessorSet, w \in WaveSet : (\A y \in WaveSet : y > w /\ waveDAG[p][y].exists => w \in waveDAG[p][y].edges) => (\A y \in WaveSet : y >= w /\ waveDAG[p][y].exists => Contains(w, commitWithRef[p][y])) 
Invariant9 == \A p,q \in ProcessorSet, w \in WaveSet : decidedWave[p] # 0 /\ w >= decidedWave[p] /\ waveDAG[q][w].exists = TRUE => Contains(decidedWave[p], commitWithRef[q][w])
Invariant10 == \A p,q \in ProcessorSet, w \in WaveSet : waveDAG[p][w].exists = TRUE /\ w >= decidedWave[q] /\ decidedWave[q] # 0 => IsPrefix(commitWithRef[q][decidedWave[q]], commitWithRef[p][w]) 

=============================================================================
\* Modification History
\* Last modified Mon Jan 15 13:11:05 AEDT 2024 by Pranav
\* Created Mon Jan 15 13:08:30 AEDT 2024 by Pranav
