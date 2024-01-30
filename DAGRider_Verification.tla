--------------------- MODULE DAGRider_Verification ---------------------

EXTENDS Integers, TLAPS, TLC, Sequences, DAGRider_Spec , FiniteSets
           
LEMMA VertexSetDef == VertexSet' = VertexSet 
      
LEMMA tailType == ASSUME NEW S \in Seq(BlockSet), S # <<>>
      PROVE Tail(S) \in Seq(BlockSet)
      
LEMMA DVinVertexSet == \A p \in ProcessorSet : DummyVertex(p) \in VertexSet  

LEMMA nvinNV == \A p \in ProcessorSet, r \in RoundSet : NilVertex(p,r) \in NilVertexSet
  
LEMMA NVnotinVertexSet == \A p \in ProcessorSet, r \in RoundSet : NilVertex(p,r) \notin VertexSet

LEMMA type_cnv == ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet
                  PROVE CreateVertex(p, r) \in VertexSet
                   
LEMMA vertexType == ASSUME NEW v \in VertexSet 
                    PROVE v \in [round : RoundSet, source : ProcessorSet, edges : SUBSET(VertexSet)]

LEMMA divprop1 == ASSUME NEW n \in Nat, NEW x \in 0..4*n, x % 4 = 1
                 PROVE (x \div 4)+1 \in 1..n
                 
LEMMA divprop2 == ASSUME NEW n \in Nat, NEW x \in 0..4*n, x % 4 = 0, x>0
                  PROVE (x \div 4) \in 1..n
                  
LEMMA 0isRound == 0 \in RoundSet
                                                     
LEMMA TypeCorrectnessLem == Spec => []StateType 
 <1>1 Init => StateType
      <2>1 0 \in RoundSet
           BY 0isRound
      <2>2 ASSUME NEW r \in RoundSet
           PROVE IF r = 0 THEN TRUE ELSE FALSE \in BOOLEAN
           OBVIOUS
      <2>3 ASSUME Init 
           PROVE dag \in [ProcessorSet -> [RoundSet  -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]
           <3>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet
                PROVE  dag[p][r][q] \in VertexSet \cup NilVertexSet
                <4>1 dag[p][r][q] =  IF r = 0 THEN DummyVertex(q) ELSE NilVertex(q,r)
                     BY <3>3,<2>3 DEF Init
                <4>2 DummyVertex(q) \in VertexSet
                     BY <3>3, DVinVertexSet
                <4>3 NilVertex(q,r) \in NilVertexSet
                     BY <3>3, nvinNV
                <4> QED BY <4>1,<4>2,<4>3
           <3> QED BY <2>3, <3>3 DEF Init
      <2> QED BY <2>1,<2>2,<2>3 DEF Init, StateType
 <1>2 ASSUME [Next]_vars, StateType
      PROVE StateType' 
      <2>1 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW v \in VertexSet, Broadcast(p,r,v)
           PROVE /\ broadcastNetwork' \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                 /\ broadcastRecord' \in [ProcessorSet -> [RoundSet -> BOOLEAN]]
           <3>1 CASE broadcastRecord[p][r] = FALSE 
                <4>1 [broadcastRecord EXCEPT ![p][r] = TRUE] \in [ProcessorSet -> [RoundSet -> BOOLEAN]]
                     BY <2>1,<1>2 DEF StateType
                <4>2 [q \in ProcessorSet \cup {"History"} |-> broadcastNetwork[q] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}] \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                     <5>1 [sender |-> p, inRound |-> r, vertex |-> v] \in TaggedVertexSet
                          BY <2>1 DEF TaggedVertexSet
                     <5> QED BY <2>1,<1>2,<5>1 DEF StateType
                <4> QED BY <4>1,<4>2,<3>1,<2>1,<1>2 DEF StateType, Broadcast
           <3>2 CASE broadcastRecord[p][r] = TRUE
                BY <3>2,<1>2,<2>1 DEF StateType, Broadcast
           <3> QED BY <3>1,<3>2,<1>2,<2>1 DEF StateType, Broadcast
      <2>2 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE StateType'
           <3>3 blocksToPropose[p] \in Seq(BlockSet)
                BY  <2>2,<1>2 DEF StateType
           <3>1  Append(blocksToPropose[p], b) \in Seq(BlockSet)
                 BY <3>3 DEF StateType
           <3>2 blocksToPropose' \in [ProcessorSet -> Seq(BlockSet)]
                BY <3>1,<2>2,<1>2 DEF ProposeTn, StateType
           <3> QED BY <3>2, <2>2,<1>2, VertexSetDef DEF ProposeTn, StateType, TaggedVertexSet
      <2>3 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE StateType'
            <3>1 [round EXCEPT ![p] = round[p]+1] \in [ProcessorSet -> RoundSet]
                 BY <2>3,<1>2 DEF NextRoundTn, StateType
            <3>2 [blocksToPropose EXCEPT ![p] = Tail(blocksToPropose[p])] \in [ProcessorSet -> Seq(BlockSet)]
                 <4>1 blocksToPropose[p] \in Seq(BlockSet) /\ blocksToPropose[p] # <<>>
                      BY <2>3,<1>2,<2>3 DEF StateType, NextRoundTn  
                 <4>2 Tail(blocksToPropose[p]) \in Seq(BlockSet)
                      BY <4>1, tailType
                 <4> QED BY <4>2,<2>3,<1>2 DEF StateType    
            <3> QED BY <3>1,<3>2, <2>3,<1>2,<2>1, VertexSetDef, type_cnv DEF NextRoundTn, StateType, TaggedVertexSet
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, NEW q \in ProcessorSet, p # q, ReceiveVertexTn(p, q, r, v)
           PROVE StateType'
           <3>1 buffer' \in [ProcessorSet -> SUBSET(VertexSet)]
                BY <2>4,<1>2 DEF StateType, ReceiveVertexTn
           <3>2 broadcastNetwork' \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                BY <2>4,<1>2 DEF StateType, ReceiveVertexTn
           <3> QED BY <3>1,<3>2, <2>4,<1>2,<2>1, VertexSetDef DEF ReceiveVertexTn, StateType, TaggedVertexSet
      <2>5 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE StateType'
           <3>1 dag' \in [ProcessorSet -> [RoundSet -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]
                <4>1 v.round \in RoundSet /\ v.source \in ProcessorSet \*/\ v.source \in ProcessorSet
                     BY vertexType, <2>5 
                <4>2 dag' = [dag EXCEPT ![p][v.round][v.source] = v]
                     BY <2>5, <1>2  DEF AddVertexTn, StateType
                <4> QED BY <4>1,<4>2,<2>5,<1>2 DEF StateType
           <3> QED BY <3>1,<2>5,<1>2, VertexSetDef DEF AddVertexTn, StateType, TaggedVertexSet
      <2>6 CASE UNCHANGED vars 
           BY <2>6,<2>1,<1>2, VertexSetDef DEF vars, TaggedVertexSet, StateType
      <2> QED  BY <2>2,<2>3,<2>4,<2>5,<2>6,<1>2 DEF Next  
 <1> QED BY <1>1,<1>2,PTL DEF Spec

\*\A p,q \in ProcessorSet, r \in RoundSet : r # 0 /\ dag[p][r][q] \in VertexSet => dag[p][r][q] \in buffer[p]
LEMMA Invariant1CorrectnessLem == Spec => []Invariant1
 <1>1 Init => Invariant1
      <2>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW r \in RoundSet, r # 0, Init
           PROVE dag[p][r][q] \notin VertexSet
           <3>1 dag[p][r][q] = NilVertex(q,r)
                BY <2>1 DEF Init
           <3> QED BY <3>1, NVnotinVertexSet
      <2> QED BY <2>1 DEF Invariant1
 <1>2 ASSUME [Next]_vars,StateType, StateType', Invariant1
      PROVE Invariant1'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant1'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant1, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant1'
           BY VertexSetDef,<2>2,<1>2 DEF Invariant1, NextRoundTn
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant1'
           <3>1 ASSUME NEW t \in ProcessorSet
                PROVE  buffer[t] \in SUBSET(buffer'[t])
                <4>1 CASE t = p
                     BY <4>1,<2>3,<1>2 DEF ReceiveVertexTn,StateType
                <4>2 CASE t # p
                     BY <4>2,<2>3,<1>2 DEF ReceiveVertexTn,StateType
                <4> QED BY <4>1,<4>2
           <3> QED BY VertexSetDef,<2>3, <1>2,<3>1 DEF Invariant1, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant1'
           <3>1 ASSUME NEW q \in ProcessorSet, NEW t \in ProcessorSet,NEW r \in RoundSet, r # 0, dag'[q][r][t] \in VertexSet
                PROVE dag'[q][r][t] \in buffer'[q]
                <4>1 CASE q = p /\ r = v.round /\ t = v.source
                     <5>1 dag'[q][r][t] = v
                          BY <4>1,<3>1,<2>4,<1>2 DEF StateType, AddVertexTn
                     <5>2 v \in buffer'[q]
                          BY <4>1,<2>4,<1>2 DEF StateType, AddVertexTn
                     <5> QED BY <5>1,<4>1,<5>2
                <4>2 CASE p # q \/ v.source # t \/ v.round # r
                     <5>1 dag'[q][r][t] = dag[q][r][t] /\ buffer'[q] = buffer[q] 
                          BY <4>2,<3>1,<2>4,<1>2 DEF AddVertexTn, StateType
                     <5> QED BY <5>1,<3>1,<1>2 DEF Invariant1
                <4> QED BY <4>1,<4>2
           <3> QED BY <3>1, VertexSetDef, <1>2 DEF Invariant1
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant1, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, TypeCorrectnessLem, PTL DEF Spec

\*\A m \in broadcastNetwork["History"]: broadcastRecord[m.sender][m.inRound] = TRUE 
LEMMA Invariant2CorrectnessLem == Spec => []Invariant2
 <1>1 Init => Invariant2
      BY DEF Init, Invariant2
 <1>2 ASSUME [Next]_vars,StateType, StateType', Invariant2
      PROVE Invariant2'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant2'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant2, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant2'
           <3>1 ASSUME NEW r \in RoundSet,NEW v \in VertexSet, Broadcast(p,r,v)
                PROVE Invariant2'
                <4>1 CASE broadcastRecord[p][r] = FALSE 
                     <5>1 broadcastNetwork'["History"] = broadcastNetwork["History"] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}
                          BY <3>1,<2>2,<1>2,<4>1 DEF StateType, Broadcast
                     <5>2 broadcastRecord' = [broadcastRecord EXCEPT ![p][r] = TRUE]
                          BY <3>1,<2>2,<1>2,<4>1 DEF StateType, Broadcast
                     <5>3 ASSUME NEW m \in broadcastNetwork'["History"]
                          PROVE broadcastRecord'[m.sender][m.inRound] = TRUE
                          <6>1 m.sender \in ProcessorSet /\ m.inRound \in RoundSet
                               <7>1 broadcastNetwork'["History"] \in SUBSET[sender : ProcessorSet, inRound : RoundSet, vertex : VertexSet']
                                    BY <1>2 DEF StateType, TaggedVertexSet
                               <7> QED BY <7>1,<5>3
                          <6>2 CASE m \in broadcastNetwork["History"]
                               <7>1 broadcastRecord[m.sender][m.inRound] = TRUE
                                    BY <6>2,<1>2 DEF Invariant2
                               <7>2 ASSUME NEW a \in ProcessorSet, NEW b \in RoundSet
                                    PROVE broadcastRecord'[a][b] = broadcastRecord[a][b] \/ broadcastRecord'[a][b] = TRUE
                                    <8>1 CASE a = p /\ b = r
                                         BY <8>1,<5>2, <1>2 DEF StateType
                                    <8>2 CASE a # p \/ b # r 
                                         BY <8>2,<5>2, <1>2 DEF StateType
                                    <8> QED BY <8>1,<8>2
                               <7> QED BY <7>1,<7>2,<6>1
                          <6>3 CASE m = [sender |-> p, inRound |-> r, vertex |-> v]
                               BY <6>3,<5>2, <1>2 DEF StateType
                          <6> QED BY <6>2,<6>3,<5>1
                     <5> QED BY <1>2,<5>3 DEF Invariant2
                <4>2 CASE broadcastRecord[p][r] = TRUE
                     <5>1 UNCHANGED <<broadcastNetwork, broadcastRecord>>
                          BY <4>2,<2>2,<3>1 DEF Broadcast
                     <5> QED BY <5>1,<1>2 DEF Invariant2
                <4> QED BY <4>1,<4>2,<3>1,<2>2,<1>2 DEF StateType 
           <3> QED BY VertexSetDef,<2>2,<1>2, type_cnv,<3>1 DEF Invariant2, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant2'
           <3>1 broadcastNetwork'["History"] =  broadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1,<2>3,<1>2 DEF StateType, ReceiveVertexTn
           <3>2 broadcastRecord' = broadcastRecord
                BY <2>3 DEF ReceiveVertexTn
           <3> QED BY <3>1,<3>2, VertexSetDef,<2>3,<1>2 DEF Invariant2, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant2'
           BY VertexSetDef,<2>4,<1>2 DEF Invariant2, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant2, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, TypeCorrectnessLem, PTL DEF Spec

LEMMA Invariant3CorrectnessLem == Spec => []Invariant3
 <1>1 Init => Invariant3
      BY DEF Init, Invariant3
 <1>2 ASSUME [Next]_vars,StateType, StateType', Invariant3
      PROVE Invariant3'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant3'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant3, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant3'
           BY VertexSetDef,<2>2,<1>2 DEF Invariant3, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant3'
           <3>1 broadcastNetwork'["History"] =  broadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1,<2>3,<1>2 DEF StateType, ReceiveVertexTn
           <3>2 \A z \in ProcessorSet : broadcastNetwork'[z] \in SUBSET(broadcastNetwork[z])
                BY <2>3,<1>2 DEF StateType, ReceiveVertexTn
           <3> QED BY <3>1,<3>2,<2>3,<1>2 DEF Invariant3, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant3'
           BY VertexSetDef,<2>4,<1>2 DEF Invariant3, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant3, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, TypeCorrectnessLem, PTL DEF Spec

LEMMA Invariant4CorrectnessLem == Spec => []Invariant4
 <1>1 Init => Invariant4
      BY DEF Init, Invariant4
 <1>2 ASSUME [Next]_vars,StateType, StateType', Invariant4,Invariant3
      PROVE Invariant4'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant4'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant4, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant4'
           BY VertexSetDef,<2>2,<1>2 DEF Invariant4, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant4'
           <3>1 broadcastNetwork'["History"] =  broadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1,<2>3,<1>2 DEF StateType, ReceiveVertexTn
           <3>2 ASSUME NEW t \in ProcessorSet, NEW u \in buffer'[t]
                PROVE [ sender |-> u.source, inRound |-> u.round, vertex |-> u] \in broadcastNetwork'["History"]
                <4>1 CASE p = t
                     <5>1 buffer'[p] = buffer[p] \cup {v}
                          BY <4>1,<2>3,<1>2 DEF StateType, ReceiveVertexTn
                     <5>2 CASE u = v
                          <6>1 [sender |-> v.source, inRound |-> v.round, vertex |-> v] \in broadcastNetwork["History"]
                               BY <2>3, <1>2 DEF ReceiveVertexTn, Invariant3
                          <6> QED BY <6>1,<5>2,<3>1
                     <5>3 CASE u # v
                          <6>1 u \in buffer[p]
                               BY <5>1,<5>3,<3>2,<4>1
                          <6> QED BY <6>1,<3>1,<3>2,<1>2 DEF Invariant4
                     <5> QED BY <5>2, <5>3
                <4>2 CASE p # t
                     <5>1 buffer'[t] = buffer[t]
                          BY <4>2,<2>3,<1>2 DEF StateType, ReceiveVertexTn
                     <5> QED BY <5>1,<3>1,<3>2,<1>2 DEF Invariant4
                <4> QED BY <4>1,<4>2
           <3> QED BY <3>2,<2>3,<1>2 DEF Invariant4, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant4'
           BY VertexSetDef,<2>4,<1>2 DEF Invariant4, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant4, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, TypeCorrectnessLem, Invariant3CorrectnessLem, PTL DEF Spec

LEMMA Invariant5CorrectnessLem == Spec => []Invariant5
 <1>1 Init => Invariant5
      BY DEF Init, Invariant5
 <1>2 ASSUME [Next]_vars,StateType, StateType', Invariant5, Invariant2
      PROVE Invariant5'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant5'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant5, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant5'
           <3>1 ASSUME NEW r \in RoundSet,NEW v \in VertexSet, Broadcast(p,r,v)
                PROVE Invariant5'
                <4>1 CASE broadcastRecord[p][r] = FALSE 
                     <5>1 broadcastNetwork'["History"] = broadcastNetwork["History"] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}
                          BY <3>1,<2>2,<1>2,<4>1 DEF StateType, Broadcast
                     <5>2 broadcastRecord' = [broadcastRecord EXCEPT ![p][r] = TRUE]
                          BY <3>1,<2>2,<1>2,<4>1 DEF StateType, Broadcast
                     <5>3 ASSUME NEW m \in broadcastNetwork'["History"], NEW o \in broadcastNetwork'["History"], m.sender = o.sender, m.inRound = o.inRound
                          PROVE m = o
                          <6>1 CASE m \in broadcastNetwork["History"] /\ o = [sender |-> p, inRound |-> r, vertex |-> v]
                               <7>1 broadcastRecord[m.sender][m.inRound] = TRUE
                                    BY <6>1,<1>2 DEF Invariant2
                               <7> QED BY <4>1,<7>1,<6>1,<5>3
                          <6>2 CASE o \in broadcastNetwork["History"] /\ m = [sender |-> p, inRound |-> r, vertex |-> v]
                               <7>1 broadcastRecord[o.sender][o.inRound] = TRUE
                                    BY <6>2,<1>2 DEF Invariant2
                               <7> QED BY <4>1,<7>1,<6>2,<5>3
                          <6>3 CASE m \in broadcastNetwork["History"] /\ o \in broadcastNetwork["History"]
                               BY <6>3, <5>3 ,<1>2 DEF Invariant5
                          <6> QED BY <6>1,<6>2,<6>3,<5>3,<5>1
                     <5> QED BY <1>2,<5>3 DEF Invariant5
                <4>2 CASE broadcastRecord[p][r] = TRUE
                     <5>1 UNCHANGED <<broadcastNetwork, broadcastRecord>>
                          BY <4>2,<2>2,<3>1 DEF Broadcast
                     <5> QED BY <5>1,<1>2 DEF Invariant5
                <4> QED BY <4>1,<4>2,<3>1,<2>2,<1>2 DEF StateType 
           <3> QED BY VertexSetDef,<2>2,<1>2, type_cnv,<3>1 DEF Invariant5, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant5'
           <3>1 broadcastNetwork'["History"] =  broadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1,<2>3,<1>2 DEF StateType, ReceiveVertexTn
           <3> QED BY <3>1,VertexSetDef,<2>3,<1>2 DEF Invariant5, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant5'
           BY VertexSetDef,<2>4,<1>2 DEF Invariant5, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant5, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, TypeCorrectnessLem,Invariant2CorrectnessLem, PTL DEF Spec
 
\* \A p,q \in ProcessorSet, r \in RoundSet: dag[p][r][q].source = q /\ dag[p][r][q].round = r
 
LEMMA Invariant6CorrectnessLem == Spec => []Invariant6
 <1>1 StateType /\ Init => Invariant6
      <2>1 ASSUME NEW q \in ProcessorSet, NEW t \in ProcessorSet, NEW r \in RoundSet, Init, StateType
           PROVE dag[q][r][t].source = t /\ dag[q][r][t].round = r
           <3>1 CASE r = 0
                <4>1 dag[q][r][t] = [round |-> r, source |-> t, block |-> "Empty", edges |-> {}]
                      BY <3>1,<2>1 DEF Init, StateType, DummyVertex
                <4>2 [round |-> r, source |-> t, block |-> "Empty", edges |-> {}].source = t /\ [round |-> r, source |-> t, block |-> "Empty", edges |-> {}].round = r
                     OBVIOUS
                <4> QED BY <4>1, <4>2  
           <3>2 CASE r # 0
                <4>1  dag[q][r][t] = [round |-> r, source |-> t, block |-> "Nil", edges |-> {}]
                      BY <3>2,<2>1 DEF Init, StateType,NilVertex
                <4>2 [round |-> r, source |-> t, block |-> "Nil", edges |-> {}].source = t /\ [round |-> r, source |-> t, block |-> "Nil", edges |-> {}].round = r
                     OBVIOUS
                <4> QED BY <4>1, <4>2 
           <3> QED BY <3>1,<3>2  
      <2> QED BY <2>1 DEF Invariant6          
 <1>2 ASSUME [Next]_vars,StateType, StateType', Invariant6
      PROVE Invariant6'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant6'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant6, ProposeTn, VertexSet
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant6'
           BY VertexSetDef,<2>2,<1>2 DEF Invariant6, NextRoundTn, VertexSet
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant6'
           BY VertexSetDef,<2>3,<1>2 DEF Invariant6, ReceiveVertexTn, VertexSet
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant6'
           <3>1 ASSUME NEW q \in ProcessorSet, NEW t \in ProcessorSet, NEW r \in RoundSet
                PROVE dag'[q][r][t].source = t /\ dag'[q][r][t].round = r
                <4>1 CASE q = p /\ r = v.round /\ t = v.source
                     <5>1 dag'[q][r][t] = v
                          BY <4>1,<3>1,<2>4,<1>2 DEF StateType, AddVertexTn
                     <5> QED BY <5>1,<4>1
                <4>2 CASE p # q \/ v.source # t \/ v.round # r
                     <5>1 dag'[q][r][t] = dag[q][r][t] 
                          BY <4>2,<3>1,<2>4,<1>2 DEF AddVertexTn, StateType 
                     <5> QED BY <5>1,<3>1,<1>2 DEF Invariant6
                <4> QED BY <4>1,<4>2, vertexType
           <3> QED BY <3>1,VertexSetDef,<2>4,<1>2 DEF Invariant6, AddVertexTn, VertexSet
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant6, vars, VertexSet
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, TypeCorrectnessLem, PTL DEF Spec

LEMMA DagConsistencyCorrectnessThm == Spec => []DagConsistency
 <1>1 Init => DagConsistency
     BY DEF Init, DagConsistency
 <1>2 Invariant1' /\ Invariant4' /\ Invariant6' /\ Invariant5' /\ DagConsistency /\ [Next]_vars => DagConsistency'
    <2> SUFFICES ASSUME DagConsistency, [Next]_vars,Invariant1',Invariant4',Invariant6', Invariant5'
                  PROVE DagConsistency'
                  OBVIOUS
    <2>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW  r \in RoundSet, NEW k \in ProcessorSet, r # 0, dag'[p][r][k] \in VertexSet, dag'[q][r][k] \in VertexSet
              PROVE dag'[p][r][k] = dag'[q][r][k]
        <3>1 CASE r = 0
             BY <3>1,<2>1
        <3>2 CASE r # 0
             <4>1 \A a, b \in ProcessorSet, z \in RoundSet : dag'[a][z][b].source = b /\ dag'[a][z][b].round = z
                  BY DEF Invariant6
             <4>2 dag'[p][r][k].source = k /\ dag'[p][r][k].round = r /\ dag'[q][r][k].source = k /\ dag'[q][r][k].round = r
                  BY <2>1,<4>1
             <4>3 \A p_1, q_1 \in ProcessorSet, r_1 \in RoundSet : r_1 # 0 /\ dag'[p_1][r_1][q_1] \in VertexSet => dag'[p_1][r_1][q_1] \in buffer'[p_1]
                  BY VertexSetDef DEF Invariant1 
             <4>4 dag'[p][r][k] \in buffer'[p] /\  dag'[q][r][k] \in buffer'[q]
                  BY <2>1,<4>3,<3>2
             <4>5 [ sender |-> k, inRound |-> r, vertex |-> dag'[p][r][k]] \in broadcastNetwork'["History"] /\ [ sender |-> k, inRound |-> r, vertex |-> dag'[q][r][k]] \in broadcastNetwork'["History"]
                  BY <2>1,<4>4, <4>2 DEF Invariant4
             <4> QED BY <4>5 DEF Invariant5
        <3> QED BY <3>1,<3>2
    <2>2 DagConsistency' = \A a,b \in ProcessorSet, z \in RoundSet, o \in ProcessorSet: z # 0 /\ dag'[a][z][o] \in VertexSet /\ dag'[b][z][o] \in VertexSet => dag'[a][z][o] = dag'[b][z][o]
         BY VertexSetDef DEF DagConsistency    
    <2>3 QED BY <2>1,<2>2 
 <1> QED BY <1>1, <1>2, PTL, Invariant1CorrectnessLem,Invariant4CorrectnessLem,Invariant5CorrectnessLem, Invariant6CorrectnessLem DEF Spec      
            

LEMMA UnchangedDefLem == WaveSet = Chain!WaveSet /\ ProcessorSet = Chain!ProcessorSet /\ NumWaveAsm = Chain!NumWaveAsm /\ NumProcessorAsm = Chain!NumProcessorAsm 
                      BY DEF  WaveSet, Chain!WaveSet, ProcessorSet, Chain!ProcessorSet, NumWaveAsm, Chain!NumWaveAsm,NumProcessorAsm, Chain!NumProcessorAsm 

LEMMA SpecCorrectnessLem == Spec => Chain!Spec   
 <1>1 Init => Chain!Init
    BY DEF Init
 <1>2 ASSUME StateType, [Next]_vars 
      PROVE Chain!Next \/ UNCHANGED Chain!vars
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Chain!Next \/ UNCHANGED Chain!vars
           BY VertexSetDef,<2>1,<1>2 DEF  ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Chain!Next \/ UNCHANGED Chain!vars
           <3>1 ASSUME NEW q \in ProcessorSet, NEW w \in WaveSet, ReadyWave(p,w)
                PROVE Chain!Next \/ UNCHANGED Chain!vars
                BY UnchangedDefLem,<3>1,<1>2 DEF ReadyWave, StateType, Chain!Next
           <3>2 CASE round[p]>0 /\ (round[p] % 4) = 0
                <4>1 round[p] \div 4 \in WaveSet
                     BY divprop2,<3>2,<1>2,<2>1,NumWaveAsm DEF StateType, WaveSet, RoundSet
                <4> QED BY <4>1,<3>2,<3>1,<2>2,<1>2 DEF NextRoundTn
           <3>3 CASE ~(round[p]>0 /\ (round[p] % 4) = 0)
                BY <3>3,<2>2 DEF NextRoundTn
           <3> QED BY <3>2,<3>3 
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Chain!Next \/ UNCHANGED Chain!vars
           BY VertexSetDef,<2>3,<1>2 DEF ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Chain!Next \/ UNCHANGED Chain!vars
           <3>1 CASE v.round % 4 = 1 /\ v.source = ChooseLeader((v.round \div 4)+1)
                <4>1 (v.round \div 4)+1 \in WaveSet
                     BY <3>1,vertexType,<2>4,NumWaveAsm, divprop1 DEF RoundSet, WaveSet
                <4>2 ConnectedWaves(p,v) \in SUBSET(WaveSet)
                     BY <2>4 DEF ConnectedWaves
                <4> QED BY <2>4,<3>1,<4>1,<4>2,UnchangedDefLem DEF AddVertexTn, Chain!Next
           <3>2 CASE v.round % 4 # 1 \/ v.source # ChooseLeader((v.round \div 4)+1)
                BY <3>2,<2>4 DEF AddVertexTn
           <3> QED BY <3>1,<3>2, vertexType \*VertexSetDef,<2>4,<1>2 DEF AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY <2>5 DEF vars, Chain!vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2,PTL, TypeCorrectnessLem DEF Spec, Chain!Spec   

THEOREM SystemTypeCorrectnessLem == Spec => []StateType_System
  BY TypeCorrectnessLem, PTL, Chain!TypeCorrectnessLem, SpecCorrectnessLem,NumWaveAsm, NumProcessorAsm DEF StateType_System

THEOREM ChainConsistancyCorrectnessThm == Spec=> []ChainConsistancy  
  BY Chain!ChainConsistancyCorrectnessThm, SpecCorrectnessLem,NumWaveAsm, NumProcessorAsm, UnchangedDefLem DEF Chain!ChainConsistancy, ChainConsistancy
THEOREM ChainMonotonicityCorrectnessThm == Spec => []ChainMonotonicity
  BY Chain!ChainMonotonicityCorrectnessThm,SpecCorrectnessLem,NumWaveAsm, NumProcessorAsm, UnchangedDefLem DEF Chain!ChainMonotonicity, ChainMonotonicity
  
=============================================================================
\* Modification History
\* Last modified Tue Jan 30 19:12:08 AEDT 2024 by Pranav
\* Created Mon Jan 15 13:07:49 AEDT 2024 by Pranav
