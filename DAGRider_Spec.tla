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

RECURSIVE InRoundVertex(_), UntilRoundVertex(_), VertexSet

DummyVertex(p) == [round |-> 0, source |-> p, block |-> "Empty", edges |-> {}]
DummyVertexSet == {DummyVertex(p) : p \in ProcessorSet}

InRoundVertex(r) == IF r = 0 
                 THEN DummyVertexSet
                 ELSE [round : {r}, source : ProcessorSet, Block : BlockSet, Neighbours : SUBSET(InRoundVertex(r-1))]
               
UntilRoundVertex(r) == IF r = 0
                   THEN InRoundVertex(r)
                   ELSE InRoundVertex(r) \cup UntilRoundVertex(r-1)
                   
VertexSet == UntilRoundVertex(4*NumWaves)

TaggedVertexSet == [sender : ProcessorSet, inRound : RoundSet, vertex : VertexSet]

NilVertex(p,r) == [round |-> r, source |-> p, block |-> "Nil", edges |-> {}]
NilVertexSet == {NilVertex(p, r) : p \in ProcessorSet, r \in RoundSet}

----------------------------------------------------------------------------

VARIABLE blocksToPropose, DAGround, DAG, BroadcastNetwork, BroadcastRecord, buffer, waveDAG, decidedRefWave, leaderSeq, commitWithRef

----------------------------------------------------------------------------

Chain  == INSTANCE LeaderConsensus_Verification WITH NumWaves <- NumWaves, NumProcessors <- NumProcessors,  waveDAG <- waveDAG, decidedRefWave <- decidedRefWave, 
                                                     leaderSeq <- leaderSeq, commitWithRef <- commitWithRef

----------------------------------------------------------------------------

TypeOK == /\ blocksToPropose \in [ProcessorSet -> Seq(BlockSet)]
          /\ DAGround \in [ProcessorSet -> RoundSet]
          /\ BroadcastNetwork \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
          /\ BroadcastRecord \in [ProcessorSet -> [RoundSet -> BOOLEAN]]
          /\ buffer \in [ProcessorSet -> SUBSET(VertexSet)]
          /\ DAG \in [ProcessorSet -> [RoundSet  -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]

TypeOK_System == TypeOK /\ Chain!TypeOK

----------------------------------------------------------------------------

Init == /\ blocksToPropose = [p \in ProcessorSet |-> <<>> ]
        /\ DAGround = [p \in ProcessorSet |-> 0]
        /\ BroadcastNetwork = [p \in ProcessorSet \cup {"History"} |-> {}]
        /\ BroadcastRecord  = [p \in ProcessorSet |-> [ r \in RoundSet |-> IF r = 0 THEN TRUE ELSE FALSE ]]
        /\ buffer = [p \in ProcessorSet |-> {}]
        /\ DAG = [p \in ProcessorSet |-> [r \in RoundSet  |-> [q \in ProcessorSet |-> IF r = 0 THEN DummyVertex(q) ELSE NilVertex(q,r)]]]
        /\ Chain!Init

----------------------------------------------------------------------------

RECURSIVE Path(_,_)

Path(u,v) == IF u = v
               THEN TRUE
               ELSE IF u.round = 0
                    THEN FALSE
                    ELSE \E x \in u.edges : Path(x,v)

AddedVertices(p,r) == {v \in VertexSet : v.round = r /\ DAG[p][r][v.source] = v}
                   
\*ChooseLeader(w) == (w % NumProcessors) + 1

WaveLeader(p, w) == DAG[p][4*w-3][ChooseLeader(w)]

ConnectedWaves(p,v) == {w \in WaveSet : Path(v,WaveLeader(p, w))}                          

CreateVertex(p, r) == [round |-> r, source |-> p, block |-> Head(blocksToPropose[p]), edges |-> AddedVertices(p,r-1)]

Broadcast(p, r, v) == IF BroadcastRecord[p][r] = FALSE 
                  THEN /\ BroadcastRecord' = [BroadcastRecord EXCEPT ![p][r] = TRUE]
                       /\ BroadcastNetwork' = [q \in ProcessorSet \cup {"History"} |-> BroadcastNetwork[q] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}]
                  ELSE UNCHANGED <<BroadcastNetwork, BroadcastRecord>>
                  
ReadyWave(p, w) == IF DAG[p][4*w-3][WaveLeader(p, w)] \in VertexSet /\ \E Q \in SUBSET(AddedVertices(p,4*w)): Cardinality(Q) > 2*NumFaultyProcessors /\ \A u \in Q : Path(u, WaveLeader(p, w))
                    THEN Chain!update_decidedRefWave(p, w)
                    ELSE UNCHANGED Chain!vars 

----------------------------------------------------------------------------

NextRoundTn(p) == /\ DAGround[p]+1 \in RoundSet
                 /\ Cardinality(AddedVertices(p,DAGround[p])) > 2*NumFaultyProcessors
                 /\ blocksToPropose[p] # <<>>
                 /\ Broadcast(p, DAGround[p]+1, CreateVertex(p,DAGround[p]+1))
                 /\ DAGround' = [DAGround EXCEPT ![p] = DAGround[p]+1]
                 /\ blocksToPropose' = [blocksToPropose EXCEPT ![p] = Tail(blocksToPropose[p])]
                 /\ IF DAGround[p]>0 /\ (DAGround[p] % 4) = 0 THEN ReadyWave(p, (DAGround[p] \div 4)) ELSE UNCHANGED Chain!vars
                 /\ UNCHANGED <<DAG,buffer>>

ProposeTn(p,b) == /\ blocksToPropose' = [blocksToPropose EXCEPT ![p] = Append(blocksToPropose[p], b)]
                /\ UNCHANGED Chain!vars
                /\ UNCHANGED <<DAGround, BroadcastNetwork, BroadcastRecord, buffer, DAG>>
                
ReceiveVertexTn(p, q, r, v) == /\ [sender |-> q, inRound |-> r, vertex |-> v] \in BroadcastNetwork[p]
                              /\ v.source = q 
                              /\ v.round = r
                              /\ Cardinality(v.edges) > 2*NumFaultyProcessors
                              /\ buffer' = [buffer EXCEPT ![p] = buffer[p] \cup {v}]
                              /\ BroadcastNetwork' = [BroadcastNetwork EXCEPT ![p] = BroadcastNetwork[p] \ {[sender |-> q, inRound |-> r, vertex |-> v]}]
                              /\ UNCHANGED Chain!vars
                              /\ UNCHANGED <<blocksToPropose, DAGround, BroadcastRecord, DAG>>

AddVertexTn(p,v) == /\ v \in buffer[p]
                   /\ v.round <= DAGround[p]
                   /\ DAG[p][v.round][v.source] = NilVertex(v.source, v.round)
                   /\ v.edges \in AddedVertices(p, v.round -1)
                   /\ DAG'= [DAG EXCEPT ![p][v.round][v.source] = v]
                   /\ IF v.round % 4 = 1 /\ v.source = ChooseLeader((v.round \div 4)+1) THEN Chain!UpdateWaveTn(p,(v.round \div 4)+1, ConnectedWaves(p,v)) ELSE UNCHANGED Chain!vars
                   /\ UNCHANGED <<blocksToPropose, DAGround, BroadcastNetwork, BroadcastRecord, buffer>>

----------------------------------------------------------------------------

Next == \E p \in ProcessorSet, r \in RoundSet, v \in VertexSet, b \in BlockSet: \E q \in ProcessorSet\{p} : \/ ProposeTn(p,b)
                                                                                       \/ NextRoundTn(p)
                                                                                       \/ ReceiveVertexTn(p, q, r, v)
                                                                                       \/ AddVertexTn(p,v)

----------------------------------------------------------------------------
                                                                                       
vars == <<blocksToPropose, DAGround, BroadcastNetwork, BroadcastRecord, buffer, DAG, waveDAG, decidedRefWave, leaderSeq, commitWithRef>>

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

DAGConsistency == \A p,q \in ProcessorSet, r \in RoundSet, o \in ProcessorSet: r # 0 /\ DAG[p][r][o] \in VertexSet /\ DAG[q][r][o] \in VertexSet => DAG[p][r][o] = DAG[q][r][o]
ChainConsistancy == \A p,q \in ProcessorSet : decidedRefWave[p] <= decidedRefWave[q] => Chain!IsPrefix(leaderSeq[p].current, leaderSeq[q].current)
ChainMonotonicity == \A p \in ProcessorSet : Chain!IsPrefix(leaderSeq[p].last, leaderSeq[p].current)

----------------------------------------------------------------------------

Invariant1 == \A p,q \in ProcessorSet, r \in RoundSet : r # 0 /\ DAG[p][r][q] \in VertexSet => DAG[p][r][q] \in buffer[p] 
Invariant2 == \A m \in BroadcastNetwork["History"]: BroadcastRecord[m.sender][m.inRound] = TRUE 
Invariant3 == \A p \in ProcessorSet: \A m \in BroadcastNetwork[p]: m \in BroadcastNetwork["History"] 
Invariant6 == \A p,q \in ProcessorSet, r \in RoundSet: DAG[p][r][q].source = q /\ DAG[p][r][q].round = r
Invariant4 == \A p \in ProcessorSet : \A v \in buffer[p] : [ sender |-> v.source, inRound |-> v.round, vertex |-> v] \in BroadcastNetwork["History"]
Invariant5 == \A m,o \in BroadcastNetwork["History"]: m.sender = o.sender /\ m.inRound = o.inRound => m = o

----------------------------------------------------------------------------

=============================================================================
\* Modification History
\* Last modified Mon Jan 15 14:16:13 AEDT 2024 by Pranav
\* Created Mon Jan 15 13:06:34 AEDT 2024 by Pranav
