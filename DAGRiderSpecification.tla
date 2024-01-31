----------------------- MODULE DAGRiderSpecification -----------------------

EXTENDS FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC

----------------------------------------------------------------------------

CONSTANT NumProcessors

ASSUME NumProcessorAsm == NumProcessors \in Nat\{0}

NumFaultyProcessors == (NumProcessors-1) \div 3

ProcessorSet == 1..NumProcessors

----------------------------------------------------------------------------

ASSUME ProcSetAsm == "History" \notin ProcessorSet

CONSTANT NumWaves

ASSUME NumWaveAsm == NumWaves \in Nat\{0}

WaveSet == 1..NumWaves

RoundSet == 0..(4*NumWaves)

----------------------------------------------------------------------------

CONSTANT BlockSet

DummyVertex(p) == [round |-> 0, source |-> p, block |-> "Empty", edges |-> {}]

DummyVertexSet == {DummyVertex(p) : p \in ProcessorSet}

RECURSIVE InRoundVertex(_)

InRoundVertex(r) == IF r = 0
                 THEN DummyVertexSet
                 ELSE [round : {r}, source : ProcessorSet, Block : BlockSet, Neighbours : SUBSET(InRoundVertex(r-1))]

RECURSIVE UntilRoundVertex(_)

UntilRoundVertex(r) == IF r = 0
                   THEN InRoundVertex(r)
                   ELSE InRoundVertex(r) \cup UntilRoundVertex(r-1)

RECURSIVE VertexSet

VertexSet == UntilRoundVertex(4*NumWaves)

TaggedVertexSet == [sender : ProcessorSet, inRound : RoundSet, vertex : VertexSet]

NilVertex(p, r) == [round |-> r, source |-> p, block |-> "Nil", edges |-> {}]

NilVertexSet == {NilVertex(p, r) : p \in ProcessorSet, r \in RoundSet}

----------------------------------------------------------------------------

VARIABLE blocksToPropose,
         round,
         dag,
         broadcastNetwork,
         broadcastRecord,
         buffer,
         leaderReachablity,
         decidedWave,
         leaderSeq,
         commitWithRef

StateType ==
          /\ blocksToPropose \in [ProcessorSet -> Seq(BlockSet)]
          /\ round \in [ProcessorSet -> RoundSet]
          /\ broadcastNetwork \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
          /\ broadcastRecord \in [ProcessorSet -> [RoundSet -> BOOLEAN]]
          /\ buffer \in [ProcessorSet -> SUBSET(VertexSet)]
          /\ dag \in [ProcessorSet -> [RoundSet  -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]

----------------------------------------------------------------------------

LeaderConsensus  == INSTANCE LeaderConsensusVerification WITH NumWaves <- NumWaves,
                                                     NumProcessors <- NumProcessors,
                                                     leaderReachablity <- leaderReachablity,
                                                     decidedWave <- decidedWave,
                                                     leaderSeq <- leaderSeq,
                                                     commitWithRef <- commitWithRef

ComposedStateType == StateType /\ LeaderConsensus!StateType

----------------------------------------------------------------------------

Init == /\ blocksToPropose = [p \in ProcessorSet |-> <<>> ]
        /\ round = [p \in ProcessorSet |-> 0]
        /\ broadcastNetwork = [p \in ProcessorSet \cup {"History"} |-> {}]
        /\ broadcastRecord  = [p \in ProcessorSet |-> [ r \in RoundSet |-> IF r = 0 THEN TRUE ELSE FALSE ]]
        /\ buffer = [p \in ProcessorSet |-> {}]
        /\ dag = [p \in ProcessorSet |-> [r \in RoundSet  |-> [q \in ProcessorSet |-> IF r = 0 THEN DummyVertex(q) ELSE NilVertex(q, r)]]]
        /\ LeaderConsensus!Init

----------------------------------------------------------------------------

CONSTANT ChooseLeader(_)

RECURSIVE Path(_, _)
Path(u, v) == IF u = v
               THEN TRUE
               ELSE IF u.round = 0
                    THEN FALSE
                    ELSE \E x \in u.edges : Path(x, v)

AddedVertices(p, r) == {v \in VertexSet : v.round = r /\ dag[p][r][v.source] = v}

\*ChooseLeader(w) == (w % NumProcessors) + 1

WaveLeader(p, w) == dag[p][4*w-3][ChooseLeader(w)]

ConnectedWaves(p, v) == {w \in WaveSet : Path(v, WaveLeader(p, w))}

CreateVertex(p, r) == [round |-> r, source |-> p, block |-> Head(blocksToPropose[p]), edges |-> AddedVertices(p, r-1)]

Broadcast(p, r, v) == IF broadcastRecord[p][r] = FALSE
                      THEN /\ broadcastRecord' = [broadcastRecord EXCEPT ![p][r] = TRUE]
                           /\ broadcastNetwork' = [q \in ProcessorSet \cup {"History"} |-> broadcastNetwork[q] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}]
                      ELSE UNCHANGED <<broadcastNetwork, broadcastRecord>>

ReadyWave(p, w) == IF dag[p][4*w-3][WaveLeader(p, w)] \in VertexSet /\ \E Q \in SUBSET(AddedVertices(p, 4*w)): Cardinality(Q) > 2*NumFaultyProcessors /\ \A u \in Q : Path(u, WaveLeader(p, w))
                   THEN LeaderConsensus!UpdateDecidedWaveTn(p, w)
                   ELSE UNCHANGED LeaderConsensus!vars

----------------------------------------------------------------------------

NextRoundTn(p) ==  /\ round[p]+1 \in RoundSet
                   /\ Cardinality(AddedVertices(p, round[p])) > 2*NumFaultyProcessors
                   /\ blocksToPropose[p] # <<>>
                   /\ Broadcast(p, round[p]+1, CreateVertex(p, round[p]+1))
                   /\ round' = [round EXCEPT ![p] = round[p]+1]
                   /\ blocksToPropose' = [blocksToPropose EXCEPT ![p] = Tail(blocksToPropose[p])]
                   /\ IF round[p]>0 /\ (round[p] % 4) = 0 THEN ReadyWave(p, (round[p] \div 4)) ELSE UNCHANGED LeaderConsensus!vars
                   /\ UNCHANGED <<dag, buffer>>

ProposeTn(p, b) == /\ blocksToPropose' = [blocksToPropose EXCEPT ![p] = Append(blocksToPropose[p], b)]
                  /\ UNCHANGED LeaderConsensus!vars
                  /\ UNCHANGED <<round, broadcastNetwork, broadcastRecord, buffer, dag>>

ReceiveVertexTn(p, q, r, v) == /\ [sender |-> q, inRound |-> r, vertex |-> v] \in broadcastNetwork[p]
                               /\ v.source = q
                               /\ v.round = r
                               /\ Cardinality(v.edges) > 2*NumFaultyProcessors
                               /\ buffer' = [buffer EXCEPT ![p] = buffer[p] \cup {v}]
                               /\ broadcastNetwork' = [broadcastNetwork EXCEPT ![p] = broadcastNetwork[p] \ {[sender |-> q, inRound |-> r, vertex |-> v]}]
                               /\ UNCHANGED LeaderConsensus!vars
                               /\ UNCHANGED <<blocksToPropose, round, broadcastRecord, dag>>

AddVertexTn(p, v) == /\ v \in buffer[p]
                    /\ v.round <= round[p]
                    /\ dag[p][v.round][v.source] = NilVertex(v.source, v.round)
                    /\ v.edges \in AddedVertices(p, v.round -1)
                    /\ dag'= [dag EXCEPT ![p][v.round][v.source] = v]
                    /\ IF v.round % 4 = 1 /\ v.source = ChooseLeader((v.round \div 4)+1) THEN LeaderConsensus!UpdateWaveTn(p, (v.round \div 4)+1, ConnectedWaves(p, v)) ELSE UNCHANGED LeaderConsensus!vars
                    /\ UNCHANGED <<blocksToPropose, round, broadcastNetwork, broadcastRecord, buffer>>

----------------------------------------------------------------------------

Next == \E p \in ProcessorSet, r \in RoundSet, v \in VertexSet, b \in BlockSet: \E q \in ProcessorSet\{p} : \/ ProposeTn(p, b)
                                                                                                            \/ NextRoundTn(p)
                                                                                                            \/ ReceiveVertexTn(p, q, r, v)
                                                                                                            \/ AddVertexTn(p, v)

----------------------------------------------------------------------------

vars == <<blocksToPropose, round, broadcastNetwork, broadcastRecord, buffer, dag, leaderReachablity, decidedWave, leaderSeq, commitWithRef>>

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

DagConsistency == \A p, q \in ProcessorSet, r \in RoundSet, o \in ProcessorSet: r # 0 /\ dag[p][r][o] \in VertexSet /\ dag[q][r][o] \in VertexSet => dag[p][r][o] = dag[q][r][o]

LeaderConsensusConsistancy == \A p, q \in ProcessorSet : decidedWave[p] <= decidedWave[q] => LeaderConsensus!IsPrefix(leaderSeq[p].current, leaderSeq[q].current)

LeaderConsensusMonotonicity == \A p \in ProcessorSet : LeaderConsensus!IsPrefix(leaderSeq[p].last, leaderSeq[p].current)

----------------------------------------------------------------------------

Invariant1 == \A p, q \in ProcessorSet, r \in RoundSet : r # 0 /\ dag[p][r][q] \in VertexSet => dag[p][r][q] \in buffer[p]

Invariant2 == \A m \in broadcastNetwork["History"]: broadcastRecord[m.sender][m.inRound] = TRUE

Invariant3 == \A p \in ProcessorSet: \A m \in broadcastNetwork[p]: m \in broadcastNetwork["History"]

Invariant6 == \A p, q \in ProcessorSet, r \in RoundSet: dag[p][r][q].source = q /\ dag[p][r][q].round = r

Invariant4 == \A p \in ProcessorSet : \A v \in buffer[p] : [ sender |-> v.source, inRound |-> v.round, vertex |-> v] \in broadcastNetwork["History"]

Invariant5 == \A m, o \in broadcastNetwork["History"]: m.sender = o.sender /\ m.inRound = o.inRound => m = o


=============================================================================
\* Modification History
\* Last modified Wed Jan 31 13:16:29 AEDT 2024 by Pranav
\* Created Wed Jan 31 13:12:03 AEDT 2024 by Pranav
