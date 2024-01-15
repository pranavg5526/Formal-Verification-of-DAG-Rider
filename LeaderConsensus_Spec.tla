------------------------ MODULE LeaderConsensus_Spec ------------------------
EXTENDS Integers, TLAPS, TLC, Sequences, FiniteSets, SequenceOps

CONSTANTS n_DAG,
          w_DAG

Proc == 1..n_DAG
Waves == 1..w_DAG
          
ASSUME nAssumption == n_DAG \in Nat\{0}
ASSUME wAssumption == w_DAG \in Nat\{0}

VARIABLES record, decidedRefWave, leaderSeq, commitWithRef

TypeOK == /\ record \in [Proc -> [Waves -> [exists : BOOLEAN, edges : SUBSET(Waves)]]]
          /\ decidedRefWave \in [Proc -> Waves \cup {0}]
          /\ leaderSeq \in [Proc -> [current : Seq(Waves), last : Seq(Waves)]]
          /\ commitWithRef \in [Proc -> [Waves -> Seq(Waves)]]

Init == /\ record = [p \in Proc |-> [w \in Waves |->[exists |-> FALSE, edges |-> {}]]]
        /\ decidedRefWave = [p \in Proc |-> 0]
        /\ leaderSeq = [p \in Proc |-> [current |-> <<>>, last |-> <<>>]]
        /\ commitWithRef = [p \in Proc |-> [w \in Waves |-> <<>>]]
        
max(E) == IF E # {} /\ Cardinality(E) \in Nat THEN CHOOSE x \in E : \A y \in E : y <= x ELSE "Error"   
  
update_record(p, w, E) == /\ record[p][w].exists = FALSE
                          /\ \A x \in E : record[p][x].exists = TRUE
                          /\ \A x \in E : x < w
                          /\ \A q \in Proc : record[q][w].exists = TRUE => record[q][w].edges = E
                          /\ \A q \in Proc : decidedRefWave[q] # 0 /\ decidedRefWave[q] < w => decidedRefWave[q] \in E
                          /\ record' = [record EXCEPT ![p][w] = [exists |-> TRUE, edges |-> E]]
                          /\ commitWithRef' = [commitWithRef EXCEPT ![p][w] = IF E = {} THEN <<w>> ELSE Append(commitWithRef[p][max(E)], w)]
                          /\ UNCHANGED <<decidedRefWave, leaderSeq>>

update_decidedRefWave(p, w) == /\ record[p][w].exists = TRUE
                               /\ w >= decidedRefWave[p]
                               /\ \A x \in Waves : x > w => record[p][x].exists = FALSE 
                               /\ \A q \in Proc, x \in Waves : x > w /\ record[q][x].exists = TRUE => w \in record[q][x].edges
                               /\ decidedRefWave' = [decidedRefWave EXCEPT ![p] = w]
                               /\ leaderSeq' = [leaderSeq EXCEPT ![p] = [current |-> commitWithRef[p][w] ,last |-> leaderSeq[p].current]]
                               /\ UNCHANGED <<record, commitWithRef>>
                               
Next == \E p \in Proc, w \in Waves, E \in SUBSET(Waves) : update_record(p, w, E) \/ update_decidedRefWave(p, w)

vars == <<record, decidedRefWave, leaderSeq, commitWithRef>>

Spec == Init /\ [][Next]_vars


ChainMonotonicity == \A p \in Proc : IsPrefix(leaderSeq[p].last, leaderSeq[p].current)

ChainConsistancy == \A p,q \in Proc : decidedRefWave[p] <= decidedRefWave[q] => IsPrefix(leaderSeq[p].current, leaderSeq[q].current)

Contains(w, S) == \E i \in 1..Len(S) : S[i]=w

Invariant1 == \A p \in Proc : decidedRefWave[p] # 0 => record[p][decidedRefWave[p]].exists = TRUE
Invariant2 == \A p \in Proc : leaderSeq[p].current = IF decidedRefWave[p] = 0 THEN <<>> ELSE commitWithRef[p][decidedRefWave[p]]
Invariant3 == \A p \in Proc, w \in Waves: \A x \in record[p][w].edges : record[p][x].exists = TRUE
Invariant4 == \A p \in Proc, w,x \in Waves : Contains(w, commitWithRef[p][x]) => record[p][w].exists = TRUE
Invariant5 == \A p \in Proc, w,x \in Waves : Contains(w, commitWithRef[p][x]) => IsPrefix(commitWithRef[p][w], commitWithRef[p][x])
Invariant6 == \A p \in Proc, w \in Waves: record[p][w].exists = TRUE => commitWithRef[p][w] = IF record[p][w].edges = {} THEN <<w>> ELSE Append(commitWithRef[p][max(record[p][w].edges)], w) 
Invariant7 == \A p, q \in Proc, w \in Waves : record[p][w].exists = record[q][w].exists => commitWithRef[p][w] = commitWithRef[q][w]
Invariant8 == \A p \in Proc, w \in Waves : (\A y \in Waves : y > w /\ record[p][y].exists => w \in record[p][y].edges) => (\A y \in Waves : y >= w /\ record[p][y].exists => Contains(w, commitWithRef[p][y])) 
Invariant9 == \A p,q \in Proc, w \in Waves : decidedRefWave[p] # 0 /\ w >= decidedRefWave[p] /\ record[q][w].exists = TRUE => Contains(decidedRefWave[p], commitWithRef[q][w])
Invariant10 == \A p,q \in Proc, w \in Waves : record[p][w].exists = TRUE /\ w >= decidedRefWave[q] /\ decidedRefWave[q] # 0 => IsPrefix(commitWithRef[q][decidedRefWave[q]], commitWithRef[p][w]) 

=============================================================================
\* Modification History
\* Last modified Mon Jan 15 13:11:05 AEDT 2024 by Pranav
\* Created Mon Jan 15 13:08:30 AEDT 2024 by Pranav
