--------------------------- MODULE DAGRider_Spec ---------------------------
EXTENDS Sequences, FiniteSets, Integers, TLAPS, TLC

CONSTANT NumProcessors,
         NumWaves, 
         BlockSet,
         ChooseLeader(_) 
         
ASSUME NumProcessorAsm == NumProcessors \in Nat\{0}
ASSUME NumWaveAsm == NumWaves \in Nat\{0}

----------------------------------------------------------------------------

NumFaultyProcessors == (NumProcessors-1) \div 3 

RoundSet == 0..(4*NumWaves)

WaveSet == 1..NumWaves

ProcessorSet == 1..NumProcessors
ASSUME ProcSetAsm == "History" \notin ProcessorSet

RECURSIVE vertices_in(_), vertices_till(_), Vertices

dummy_vertex(p) == [round |-> 0, source |-> p, block |-> "Empty", edges |-> {}]
DummyVertices == {dummy_vertex(p) : p \in ProcessorSet}

vertices_in(r) == IF r = 0 
                 THEN DummyVertices
                 ELSE [round : {r}, source : ProcessorSet, Block : BlockSet, Neighbours : SUBSET(vertices_in(r-1))]
               
vertices_till(r) == IF r = 0
                   THEN vertices_in(r)
                   ELSE vertices_in(r) \cup vertices_till(r-1)
                   
Vertices == vertices_till(4*NumWaves)

TaggedVertices == [sender : ProcessorSet, inRound : RoundSet, vertex : Vertices]

nil_vertex(p,r) == [round |-> r, source |-> p, block |-> "Nil", edges |-> {}]
NilVertices == {nil_vertex(p, r) : p \in ProcessorSet, r \in RoundSet}

----------------------------------------------------------------------------

VARIABLE blocksToPropose, DAGround, DAG, bcastNetwork, bcastRecord, buffer, record, decidedRefWave, leaderSeq, commitWithRef

----------------------------------------------------------------------------

Chain  == INSTANCE LeaderConsensus_Verification WITH NumWaves <- NumWaves, NumProcessors <- NumProcessors,  record <- record, decidedRefWave <- decidedRefWave, 
                                                     leaderSeq <- leaderSeq, commitWithRef <- commitWithRef

----------------------------------------------------------------------------

TypeOK == /\ blocksToPropose \in [ProcessorSet -> Seq(BlockSet)]
          /\ DAGround \in [ProcessorSet -> RoundSet]
          /\ bcastNetwork \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertices)]
          /\ bcastRecord \in [ProcessorSet -> [RoundSet -> BOOLEAN]]
          /\ buffer \in [ProcessorSet -> SUBSET(Vertices)]
          /\ DAG \in [ProcessorSet -> [RoundSet  -> [ProcessorSet -> Vertices \cup NilVertices]]]

TypeOK_System == TypeOK /\ Chain!TypeOK

----------------------------------------------------------------------------

Init == /\ blocksToPropose = [p \in ProcessorSet |-> <<>> ]
        /\ DAGround = [p \in ProcessorSet |-> 0]
        /\ bcastNetwork = [p \in ProcessorSet \cup {"History"} |-> {}]
        /\ bcastRecord  = [p \in ProcessorSet |-> [ r \in RoundSet |-> IF r = 0 THEN TRUE ELSE FALSE ]]
        /\ buffer = [p \in ProcessorSet |-> {}]
        /\ DAG = [p \in ProcessorSet |-> [r \in RoundSet  |-> [q \in ProcessorSet |-> IF r = 0 THEN dummy_vertex(q) ELSE nil_vertex(q,r)]]]
        /\ Chain!Init

----------------------------------------------------------------------------

RECURSIVE path(_,_)

path(u,v) == IF u = v
               THEN TRUE
               ELSE IF u.round = 0
                    THEN FALSE
                    ELSE \E x \in u.edges : path(x,v)

added_vertices(p,r) == {v \in Vertices : v.round = r /\ DAG[p][r][v.source] = v}
                   
\*ChooseLeader(w) == (w % NumProcessors) + 1

wave_vertex_leader(p, w) == DAG[p][4*w-3][ChooseLeader(w)]

waves_with_paths(p,v) == {w \in WaveSet : path(v,wave_vertex_leader(p, w))}                          

create_new_vertex(p, r) == [round |-> r, source |-> p, block |-> Head(blocksToPropose[p]), edges |-> added_vertices(p,r-1)]

bcast(p, r, v) == IF bcastRecord[p][r] = FALSE 
                  THEN /\ bcastRecord' = [bcastRecord EXCEPT ![p][r] = TRUE]
                       /\ bcastNetwork' = [q \in ProcessorSet \cup {"History"} |-> bcastNetwork[q] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}]
                  ELSE UNCHANGED <<bcastNetwork, bcastRecord>>
                  
wave_ready(p, w) == IF DAG[p][4*w-3][wave_vertex_leader(p, w)] \in Vertices /\ \E Q \in SUBSET(added_vertices(p,4*w)): Cardinality(Q) > 2NumFaultyProcessors /\ \A u \in Q : path(u, wave_vertex_leader(p, w))
                    THEN Chain!update_decidedRefWave(p, w)
                    ELSE UNCHANGED Chain!vars 

----------------------------------------------------------------------------

next_round(p) == /\ DAGround[p]+1 \in RoundSet
                 /\ Cardinality(added_vertices(p,DAGround[p])) > 2NumFaultyProcessors
                 /\ blocksToPropose[p] # <<>>
                 /\ bcast(p, DAGround[p]+1, create_new_vertex(p,DAGround[p]+1))
                 /\ DAGround' = [DAGround EXCEPT ![p] = DAGround[p]+1]
                 /\ blocksToPropose' = [blocksToPropose EXCEPT ![p] = Tail(blocksToPropose[p])]
                 /\ IF DAGround[p]>0 /\ (DAGround[p] % 4) = 0 THEN wave_ready(p, (DAGround[p] \div 4)) ELSE UNCHANGED Chain!vars
                 /\ UNCHANGED <<DAG,buffer>>

propose(p,b) == /\ blocksToPropose' = [blocksToPropose EXCEPT ![p] = Append(blocksToPropose[p], b)]
                /\ UNCHANGED Chain!vars
                /\ UNCHANGED <<DAGround, bcastNetwork, bcastRecord, buffer, DAG>>
                
recieve_vertex(p, q, r, v) == /\ [sender |-> q, inRound |-> r, vertex |-> v] \in bcastNetwork[p]
                              /\ v.source = q 
                              /\ v.round = r
                              /\ Cardinality(v.edges) > 2NumFaultyProcessors
                              /\ buffer' = [buffer EXCEPT ![p] = buffer[p] \cup {v}]
                              /\ bcastNetwork' = [bcastNetwork EXCEPT ![p] = bcastNetwork[p] \ {[sender |-> q, inRound |-> r, vertex |-> v]}]
                              /\ UNCHANGED Chain!vars
                              /\ UNCHANGED <<blocksToPropose, DAGround, bcastRecord, DAG>>

add_vertex(p,v) == /\ v \in buffer[p]
                   /\ v.round <= DAGround[p]
                   /\ DAG[p][v.round][v.source] = nil_vertex(v.source, v.round)
                   /\ v.edges \in added_vertices(p, v.round -1)
                   /\ DAG'= [DAG EXCEPT ![p][v.round][v.source] = v]
                   /\ IF v.round % 4 = 1 /\ v.source = ChooseLeader((v.round \div 4)+1) THEN Chain!update_record(p,(v.round \div 4)+1, waves_with_paths(p,v)) ELSE UNCHANGED Chain!vars
                   /\ UNCHANGED <<blocksToPropose, DAGround, bcastNetwork, bcastRecord, buffer>>

----------------------------------------------------------------------------

Next == \E p \in ProcessorSet, r \in RoundSet, v \in Vertices, b \in BlockSet: \E q \in ProcessorSet\{p} : \/ propose(p,b)
                                                                                       \/ next_round(p)
                                                                                       \/ recieve_vertex(p, q, r, v)
                                                                                       \/ add_vertex(p,v)

----------------------------------------------------------------------------
                                                                                       
vars == <<blocksToPropose, DAGround, bcastNetwork, bcastRecord, buffer, DAG, record, decidedRefWave, leaderSeq, commitWithRef>>

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

DAGConsistency == \A p,q \in ProcessorSet, r \in RoundSet, o \in ProcessorSet: r # 0 /\ DAG[p][r][o] \in Vertices /\ DAG[q][r][o] \in Vertices => DAG[p][r][o] = DAG[q][r][o]
ChainConsistancy == \A p,q \in ProcessorSet : decidedRefWave[p] <= decidedRefWave[q] => Chain!IsPrefix(leaderSeq[p].current, leaderSeq[q].current)
ChainMonotonicity == \A p \in ProcessorSet : Chain!IsPrefix(leaderSeq[p].last, leaderSeq[p].current)

----------------------------------------------------------------------------

Invariant1 == \A p,q \in ProcessorSet, r \in RoundSet : r # 0 /\ DAG[p][r][q] \in Vertices => DAG[p][r][q] \in buffer[p] 
Invariant2 == \A m \in bcastNetwork["History"]: bcastRecord[m.sender][m.inRound] = TRUE 
Invariant3 == \A p \in ProcessorSet: \A m \in bcastNetwork[p]: m \in bcastNetwork["History"] 
Invariant6 == \A p,q \in ProcessorSet, r \in RoundSet: DAG[p][r][q].source = q /\ DAG[p][r][q].round = r
Invariant4 == \A p \in ProcessorSet : \A v \in buffer[p] : [ sender |-> v.source, inRound |-> v.round, vertex |-> v] \in bcastNetwork["History"]
Invariant5 == \A m,o \in bcastNetwork["History"]: m.sender = o.sender /\ m.inRound = o.inRound => m = o

----------------------------------------------------------------------------

=============================================================================
\* Modification History
\* Last modified Mon Jan 15 14:16:13 AEDT 2024 by Pranav
\* Created Mon Jan 15 13:06:34 AEDT 2024 by Pranav
