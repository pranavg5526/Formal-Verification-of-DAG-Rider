----------------------- MODULE DAGRider_Verification -----------------------
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
                                                     
LEMMA Typecorrectness == Spec => []TypeOK 
 <1>1 Init => TypeOK
      <2>1 0 \in RoundSet
           BY 0isRound
      <2>2 ASSUME NEW r \in RoundSet
           PROVE IF r = 0 THEN TRUE ELSE FALSE \in BOOLEAN
           OBVIOUS
      <2>3 ASSUME Init 
           PROVE DAG \in [ProcessorSet -> [RoundSet  -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]
           <3>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet
                PROVE  DAG[p][r][q] \in VertexSet \cup NilVertexSet
                <4>1 DAG[p][r][q] =  IF r = 0 THEN DummyVertex(q) ELSE NilVertex(q,r)
                     BY <3>3,<2>3 DEF Init
                <4>2 DummyVertex(q) \in VertexSet
                     BY <3>3, DVinVertexSet
                <4>3 NilVertex(q,r) \in NilVertexSet
                     BY <3>3, nvinNV
                <4> QED BY <4>1,<4>2,<4>3
           <3> QED BY <2>3, <3>3 DEF Init
      <2> QED BY <2>1,<2>2,<2>3 DEF Init, TypeOK
 <1>2 ASSUME [Next]_vars, TypeOK
      PROVE TypeOK' 
      <2>1 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW v \in VertexSet, Broadcast(p,r,v)
           PROVE /\ BroadcastNetwork' \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                 /\ BroadcastRecord' \in [ProcessorSet -> [RoundSet -> BOOLEAN]]
           <3>1 CASE BroadcastRecord[p][r] = FALSE 
                <4>1 [BroadcastRecord EXCEPT ![p][r] = TRUE] \in [ProcessorSet -> [RoundSet -> BOOLEAN]]
                     BY <2>1,<1>2 DEF TypeOK
                <4>2 [q \in ProcessorSet \cup {"History"} |-> BroadcastNetwork[q] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}] \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                     <5>1 [sender |-> p, inRound |-> r, vertex |-> v] \in TaggedVertexSet
                          BY <2>1 DEF TaggedVertexSet
                     <5> QED BY <2>1,<1>2,<5>1 DEF TypeOK
                <4> QED BY <4>1,<4>2,<3>1,<2>1,<1>2 DEF TypeOK, Broadcast
           <3>2 CASE BroadcastRecord[p][r] = TRUE
                BY <3>2,<1>2,<2>1 DEF TypeOK, Broadcast
           <3> QED BY <3>1,<3>2,<1>2,<2>1 DEF TypeOK, Broadcast
      <2>2 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE TypeOK'
           <3>3 blocksToPropose[p] \in Seq(BlockSet)
                BY  <2>2,<1>2 DEF TypeOK
           <3>1  Append(blocksToPropose[p], b) \in Seq(BlockSet)
                 BY <3>3 DEF TypeOK
           <3>2 blocksToPropose' \in [ProcessorSet -> Seq(BlockSet)]
                BY <3>1,<2>2,<1>2 DEF ProposeTn, TypeOK
           <3> QED BY <3>2, <2>2,<1>2, VertexSetDef DEF ProposeTn, TypeOK, TaggedVertexSet
      <2>3 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE TypeOK'
            <3>1 [DAGround EXCEPT ![p] = DAGround[p]+1] \in [ProcessorSet -> RoundSet]
                 BY <2>3,<1>2 DEF NextRoundTn, TypeOK
            <3>2 [blocksToPropose EXCEPT ![p] = Tail(blocksToPropose[p])] \in [ProcessorSet -> Seq(BlockSet)]
                 <4>1 blocksToPropose[p] \in Seq(BlockSet) /\ blocksToPropose[p] # <<>>
                      BY <2>3,<1>2,<2>3 DEF TypeOK, NextRoundTn  
                 <4>2 Tail(blocksToPropose[p]) \in Seq(BlockSet)
                      BY <4>1, tailType
                 <4> QED BY <4>2,<2>3,<1>2 DEF TypeOK    
            <3> QED BY <3>1,<3>2, <2>3,<1>2,<2>1, VertexSetDef, type_cnv DEF NextRoundTn, TypeOK, TaggedVertexSet
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, NEW q \in ProcessorSet, p # q, ReceiveVertexTn(p, q, r, v)
           PROVE TypeOK'
           <3>1 buffer' \in [ProcessorSet -> SUBSET(VertexSet)]
                BY <2>4,<1>2 DEF TypeOK, ReceiveVertexTn
           <3>2 BroadcastNetwork' \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                BY <2>4,<1>2 DEF TypeOK, ReceiveVertexTn
           <3> QED BY <3>1,<3>2, <2>4,<1>2,<2>1, VertexSetDef DEF ReceiveVertexTn, TypeOK, TaggedVertexSet
      <2>5 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE TypeOK'
           <3>1 DAG' \in [ProcessorSet -> [RoundSet -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]
                <4>1 v.round \in RoundSet /\ v.source \in ProcessorSet \*/\ v.source \in ProcessorSet
                     BY vertexType, <2>5 
                <4>2 DAG' = [DAG EXCEPT ![p][v.round][v.source] = v]
                     BY <2>5, <1>2  DEF AddVertexTn, TypeOK
                <4> QED BY <4>1,<4>2,<2>5,<1>2 DEF TypeOK
           <3> QED BY <3>1,<2>5,<1>2, VertexSetDef DEF AddVertexTn, TypeOK, TaggedVertexSet
      <2>6 CASE UNCHANGED vars 
           BY <2>6,<2>1,<1>2, VertexSetDef DEF vars, TaggedVertexSet, TypeOK
      <2> QED  BY <2>2,<2>3,<2>4,<2>5,<2>6,<1>2 DEF Next  
 <1> QED BY <1>1,<1>2,PTL DEF Spec

\*\A p,q \in ProcessorSet, r \in RoundSet : r # 0 /\ DAG[p][r][q] \in VertexSet => DAG[p][r][q] \in buffer[p]
LEMMA Invariant1correctness == Spec => []Invariant1
 <1>1 Init => Invariant1
      <2>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW r \in RoundSet, r # 0, Init
           PROVE DAG[p][r][q] \notin VertexSet
           <3>1 DAG[p][r][q] = NilVertex(q,r)
                BY <2>1 DEF Init
           <3> QED BY <3>1, NVnotinVertexSet
      <2> QED BY <2>1 DEF Invariant1
 <1>2 ASSUME [Next]_vars,TypeOK, TypeOK', Invariant1
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
                     BY <4>1,<2>3,<1>2 DEF ReceiveVertexTn,TypeOK
                <4>2 CASE t # p
                     BY <4>2,<2>3,<1>2 DEF ReceiveVertexTn,TypeOK
                <4> QED BY <4>1,<4>2
           <3> QED BY VertexSetDef,<2>3, <1>2,<3>1 DEF Invariant1, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant1'
           <3>1 ASSUME NEW q \in ProcessorSet, NEW t \in ProcessorSet,NEW r \in RoundSet, r # 0, DAG'[q][r][t] \in VertexSet
                PROVE DAG'[q][r][t] \in buffer'[q]
                <4>1 CASE q = p /\ r = v.round /\ t = v.source
                     <5>1 DAG'[q][r][t] = v
                          BY <4>1,<3>1,<2>4,<1>2 DEF TypeOK, AddVertexTn
                     <5>2 v \in buffer'[q]
                          BY <4>1,<2>4,<1>2 DEF TypeOK, AddVertexTn
                     <5> QED BY <5>1,<4>1,<5>2
                <4>2 CASE p # q \/ v.source # t \/ v.round # r
                     <5>1 DAG'[q][r][t] = DAG[q][r][t] /\ buffer'[q] = buffer[q] 
                          BY <4>2,<3>1,<2>4,<1>2 DEF AddVertexTn, TypeOK
                     <5> QED BY <5>1,<3>1,<1>2 DEF Invariant1
                <4> QED BY <4>1,<4>2
           <3> QED BY <3>1, VertexSetDef, <1>2 DEF Invariant1
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant1, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, Typecorrectness, PTL DEF Spec

\*\A m \in BroadcastNetwork["History"]: BroadcastRecord[m.sender][m.inRound] = TRUE 
LEMMA Invariant2correctness == Spec => []Invariant2
 <1>1 Init => Invariant2
      BY DEF Init, Invariant2
 <1>2 ASSUME [Next]_vars,TypeOK, TypeOK', Invariant2
      PROVE Invariant2'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant2'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant2, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant2'
           <3>1 ASSUME NEW r \in RoundSet,NEW v \in VertexSet, Broadcast(p,r,v)
                PROVE Invariant2'
                <4>1 CASE BroadcastRecord[p][r] = FALSE 
                     <5>1 BroadcastNetwork'["History"] = BroadcastNetwork["History"] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}
                          BY <3>1,<2>2,<1>2,<4>1 DEF TypeOK, Broadcast
                     <5>2 BroadcastRecord' = [BroadcastRecord EXCEPT ![p][r] = TRUE]
                          BY <3>1,<2>2,<1>2,<4>1 DEF TypeOK, Broadcast
                     <5>3 ASSUME NEW m \in BroadcastNetwork'["History"]
                          PROVE BroadcastRecord'[m.sender][m.inRound] = TRUE
                          <6>1 m.sender \in ProcessorSet /\ m.inRound \in RoundSet
                               <7>1 BroadcastNetwork'["History"] \in SUBSET[sender : ProcessorSet, inRound : RoundSet, vertex : VertexSet']
                                    BY <1>2 DEF TypeOK, TaggedVertexSet
                               <7> QED BY <7>1,<5>3
                          <6>2 CASE m \in BroadcastNetwork["History"]
                               <7>1 BroadcastRecord[m.sender][m.inRound] = TRUE
                                    BY <6>2,<1>2 DEF Invariant2
                               <7>2 ASSUME NEW a \in ProcessorSet, NEW b \in RoundSet
                                    PROVE BroadcastRecord'[a][b] = BroadcastRecord[a][b] \/ BroadcastRecord'[a][b] = TRUE
                                    <8>1 CASE a = p /\ b = r
                                         BY <8>1,<5>2, <1>2 DEF TypeOK
                                    <8>2 CASE a # p \/ b # r 
                                         BY <8>2,<5>2, <1>2 DEF TypeOK
                                    <8> QED BY <8>1,<8>2
                               <7> QED BY <7>1,<7>2,<6>1
                          <6>3 CASE m = [sender |-> p, inRound |-> r, vertex |-> v]
                               BY <6>3,<5>2, <1>2 DEF TypeOK
                          <6> QED BY <6>2,<6>3,<5>1
                     <5> QED BY <1>2,<5>3 DEF Invariant2
                <4>2 CASE BroadcastRecord[p][r] = TRUE
                     <5>1 UNCHANGED <<BroadcastNetwork, BroadcastRecord>>
                          BY <4>2,<2>2,<3>1 DEF Broadcast
                     <5> QED BY <5>1,<1>2 DEF Invariant2
                <4> QED BY <4>1,<4>2,<3>1,<2>2,<1>2 DEF TypeOK 
           <3> QED BY VertexSetDef,<2>2,<1>2, type_cnv,<3>1 DEF Invariant2, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant2'
           <3>1 BroadcastNetwork'["History"] =  BroadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1,<2>3,<1>2 DEF TypeOK, ReceiveVertexTn
           <3>2 BroadcastRecord' = BroadcastRecord
                BY <2>3 DEF ReceiveVertexTn
           <3> QED BY <3>1,<3>2, VertexSetDef,<2>3,<1>2 DEF Invariant2, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant2'
           BY VertexSetDef,<2>4,<1>2 DEF Invariant2, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant2, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, Typecorrectness, PTL DEF Spec

LEMMA Invariant3correctness == Spec => []Invariant3
 <1>1 Init => Invariant3
      BY DEF Init, Invariant3
 <1>2 ASSUME [Next]_vars,TypeOK, TypeOK', Invariant3
      PROVE Invariant3'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant3'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant3, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant3'
           BY VertexSetDef,<2>2,<1>2 DEF Invariant3, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant3'
           <3>1 BroadcastNetwork'["History"] =  BroadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1,<2>3,<1>2 DEF TypeOK, ReceiveVertexTn
           <3>2 \A z \in ProcessorSet : BroadcastNetwork'[z] \in SUBSET(BroadcastNetwork[z])
                BY <2>3,<1>2 DEF TypeOK, ReceiveVertexTn
           <3> QED BY <3>1,<3>2,<2>3,<1>2 DEF Invariant3, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant3'
           BY VertexSetDef,<2>4,<1>2 DEF Invariant3, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant3, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, Typecorrectness, PTL DEF Spec

LEMMA Invariant4correctness == Spec => []Invariant4
 <1>1 Init => Invariant4
      BY DEF Init, Invariant4
 <1>2 ASSUME [Next]_vars,TypeOK, TypeOK', Invariant4,Invariant3
      PROVE Invariant4'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant4'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant4, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant4'
           BY VertexSetDef,<2>2,<1>2 DEF Invariant4, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant4'
           <3>1 BroadcastNetwork'["History"] =  BroadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1,<2>3,<1>2 DEF TypeOK, ReceiveVertexTn
           <3>2 ASSUME NEW t \in ProcessorSet, NEW u \in buffer'[t]
                PROVE [ sender |-> u.source, inRound |-> u.round, vertex |-> u] \in BroadcastNetwork'["History"]
                <4>1 CASE p = t
                     <5>1 buffer'[p] = buffer[p] \cup {v}
                          BY <4>1,<2>3,<1>2 DEF TypeOK, ReceiveVertexTn
                     <5>2 CASE u = v
                          <6>1 [sender |-> v.source, inRound |-> v.round, vertex |-> v] \in BroadcastNetwork["History"]
                               BY <2>3, <1>2 DEF ReceiveVertexTn, Invariant3
                          <6> QED BY <6>1,<5>2,<3>1
                     <5>3 CASE u # v
                          <6>1 u \in buffer[p]
                               BY <5>1,<5>3,<3>2,<4>1
                          <6> QED BY <6>1,<3>1,<3>2,<1>2 DEF Invariant4
                     <5> QED BY <5>2, <5>3
                <4>2 CASE p # t
                     <5>1 buffer'[t] = buffer[t]
                          BY <4>2,<2>3,<1>2 DEF TypeOK, ReceiveVertexTn
                     <5> QED BY <5>1,<3>1,<3>2,<1>2 DEF Invariant4
                <4> QED BY <4>1,<4>2
           <3> QED BY <3>2,<2>3,<1>2 DEF Invariant4, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant4'
           BY VertexSetDef,<2>4,<1>2 DEF Invariant4, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant4, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, Typecorrectness, Invariant3correctness, PTL DEF Spec

LEMMA Invariant5correctness == Spec => []Invariant5
 <1>1 Init => Invariant5
      BY DEF Init, Invariant5
 <1>2 ASSUME [Next]_vars,TypeOK, TypeOK', Invariant5, Invariant2
      PROVE Invariant5'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Invariant5'
           BY VertexSetDef,<2>1,<1>2 DEF Invariant5, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Invariant5'
           <3>1 ASSUME NEW r \in RoundSet,NEW v \in VertexSet, Broadcast(p,r,v)
                PROVE Invariant5'
                <4>1 CASE BroadcastRecord[p][r] = FALSE 
                     <5>1 BroadcastNetwork'["History"] = BroadcastNetwork["History"] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}
                          BY <3>1,<2>2,<1>2,<4>1 DEF TypeOK, Broadcast
                     <5>2 BroadcastRecord' = [BroadcastRecord EXCEPT ![p][r] = TRUE]
                          BY <3>1,<2>2,<1>2,<4>1 DEF TypeOK, Broadcast
                     <5>3 ASSUME NEW m \in BroadcastNetwork'["History"], NEW o \in BroadcastNetwork'["History"], m.sender = o.sender, m.inRound = o.inRound
                          PROVE m = o
                          <6>1 CASE m \in BroadcastNetwork["History"] /\ o = [sender |-> p, inRound |-> r, vertex |-> v]
                               <7>1 BroadcastRecord[m.sender][m.inRound] = TRUE
                                    BY <6>1,<1>2 DEF Invariant2
                               <7> QED BY <4>1,<7>1,<6>1,<5>3
                          <6>2 CASE o \in BroadcastNetwork["History"] /\ m = [sender |-> p, inRound |-> r, vertex |-> v]
                               <7>1 BroadcastRecord[o.sender][o.inRound] = TRUE
                                    BY <6>2,<1>2 DEF Invariant2
                               <7> QED BY <4>1,<7>1,<6>2,<5>3
                          <6>3 CASE m \in BroadcastNetwork["History"] /\ o \in BroadcastNetwork["History"]
                               BY <6>3, <5>3 ,<1>2 DEF Invariant5
                          <6> QED BY <6>1,<6>2,<6>3,<5>3,<5>1
                     <5> QED BY <1>2,<5>3 DEF Invariant5
                <4>2 CASE BroadcastRecord[p][r] = TRUE
                     <5>1 UNCHANGED <<BroadcastNetwork, BroadcastRecord>>
                          BY <4>2,<2>2,<3>1 DEF Broadcast
                     <5> QED BY <5>1,<1>2 DEF Invariant5
                <4> QED BY <4>1,<4>2,<3>1,<2>2,<1>2 DEF TypeOK 
           <3> QED BY VertexSetDef,<2>2,<1>2, type_cnv,<3>1 DEF Invariant5, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p,q,r,v)
           PROVE Invariant5'
           <3>1 BroadcastNetwork'["History"] =  BroadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1,<2>3,<1>2 DEF TypeOK, ReceiveVertexTn
           <3> QED BY <3>1,VertexSetDef,<2>3,<1>2 DEF Invariant5, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p,v)
           PROVE Invariant5'
           BY VertexSetDef,<2>4,<1>2 DEF Invariant5, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant5, vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, Typecorrectness,Invariant2correctness, PTL DEF Spec
 
\* \A p,q \in ProcessorSet, r \in RoundSet: DAG[p][r][q].source = q /\ DAG[p][r][q].round = r
 
LEMMA Invariant6correctness == Spec => []Invariant6
 <1>1 TypeOK /\ Init => Invariant6
      <2>1 ASSUME NEW q \in ProcessorSet, NEW t \in ProcessorSet, NEW r \in RoundSet, Init, TypeOK
           PROVE DAG[q][r][t].source = t /\ DAG[q][r][t].round = r
           <3>1 CASE r = 0
                <4>1 DAG[q][r][t] = [round |-> r, source |-> t, block |-> "Empty", edges |-> {}]
                      BY <3>1,<2>1 DEF Init, TypeOK, DummyVertex
                <4>2 [round |-> r, source |-> t, block |-> "Empty", edges |-> {}].source = t /\ [round |-> r, source |-> t, block |-> "Empty", edges |-> {}].round = r
                     OBVIOUS
                <4> QED BY <4>1, <4>2  
           <3>2 CASE r # 0
                <4>1  DAG[q][r][t] = [round |-> r, source |-> t, block |-> "Nil", edges |-> {}]
                      BY <3>2,<2>1 DEF Init, TypeOK,NilVertex
                <4>2 [round |-> r, source |-> t, block |-> "Nil", edges |-> {}].source = t /\ [round |-> r, source |-> t, block |-> "Nil", edges |-> {}].round = r
                     OBVIOUS
                <4> QED BY <4>1, <4>2 
           <3> QED BY <3>1,<3>2  
      <2> QED BY <2>1 DEF Invariant6          
 <1>2 ASSUME [Next]_vars,TypeOK, TypeOK', Invariant6
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
                PROVE DAG'[q][r][t].source = t /\ DAG'[q][r][t].round = r
                <4>1 CASE q = p /\ r = v.round /\ t = v.source
                     <5>1 DAG'[q][r][t] = v
                          BY <4>1,<3>1,<2>4,<1>2 DEF TypeOK, AddVertexTn
                     <5> QED BY <5>1,<4>1
                <4>2 CASE p # q \/ v.source # t \/ v.round # r
                     <5>1 DAG'[q][r][t] = DAG[q][r][t] 
                          BY <4>2,<3>1,<2>4,<1>2 DEF AddVertexTn, TypeOK 
                     <5> QED BY <5>1,<3>1,<1>2 DEF Invariant6
                <4> QED BY <4>1,<4>2, vertexType
           <3> QED BY <3>1,VertexSetDef,<2>4,<1>2 DEF Invariant6, AddVertexTn, VertexSet
      <2>5 CASE UNCHANGED vars
           BY VertexSetDef,<2>5,<1>2 DEF Invariant6, vars, VertexSet
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2, Typecorrectness, PTL DEF Spec
LEMMA DAGConsistencycorrectness == Spec => []DAGConsistency
 <1>1 Init => DAGConsistency
     BY DEF Init, DAGConsistency
 <1>2 Invariant1' /\ Invariant4' /\ Invariant6' /\ Invariant5' /\ DAGConsistency /\ [Next]_vars => DAGConsistency'
    <2> SUFFICES ASSUME DAGConsistency, [Next]_vars,Invariant1',Invariant4',Invariant6', Invariant5'
                  PROVE DAGConsistency'
                  OBVIOUS
    <2>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW  r \in RoundSet, NEW k \in ProcessorSet, r # 0, DAG'[p][r][k] \in VertexSet, DAG'[q][r][k] \in VertexSet
              PROVE DAG'[p][r][k] = DAG'[q][r][k]
        <3>1 CASE r = 0
             BY <3>1,<2>1
        <3>2 CASE r # 0
             <4>1 \A a, b \in ProcessorSet, z \in RoundSet : DAG'[a][z][b].source = b /\ DAG'[a][z][b].round = z
                  BY DEF Invariant6
             <4>2 DAG'[p][r][k].source = k /\ DAG'[p][r][k].round = r /\ DAG'[q][r][k].source = k /\ DAG'[q][r][k].round = r
                  BY <2>1,<4>1
             <4>3 \A p_1, q_1 \in ProcessorSet, r_1 \in RoundSet : r_1 # 0 /\ DAG'[p_1][r_1][q_1] \in VertexSet => DAG'[p_1][r_1][q_1] \in buffer'[p_1]
                  BY VertexSetDef DEF Invariant1 
             <4>4 DAG'[p][r][k] \in buffer'[p] /\  DAG'[q][r][k] \in buffer'[q]
                  BY <2>1,<4>3,<3>2
             <4>5 [ sender |-> k, inRound |-> r, vertex |-> DAG'[p][r][k]] \in BroadcastNetwork'["History"] /\ [ sender |-> k, inRound |-> r, vertex |-> DAG'[q][r][k]] \in BroadcastNetwork'["History"]
                  BY <2>1,<4>4, <4>2 DEF Invariant4
             <4> QED BY <4>5 DEF Invariant5
        <3> QED BY <3>1,<3>2
    <2>2 DAGConsistency' = \A a,b \in ProcessorSet, z \in RoundSet, o \in ProcessorSet: z # 0 /\ DAG'[a][z][o] \in VertexSet /\ DAG'[b][z][o] \in VertexSet => DAG'[a][z][o] = DAG'[b][z][o]
         BY VertexSetDef DEF DAGConsistency    
    <2>3 QED BY <2>1,<2>2 
 <1> QED BY <1>1, <1>2, PTL, Invariant1correctness,Invariant4correctness,Invariant5correctness, Invariant6correctness DEF Spec      
            

LEMMA unchangedDef == WaveSet = Chain!WaveSet /\ ProcessorSet = Chain!ProcessorSet /\ NumWaveAsm = Chain!NumWaveAsm /\ NumProcessorAsm = Chain!NumProcessorAsm 
                      BY DEF  WaveSet, Chain!WaveSet, ProcessorSet, Chain!ProcessorSet, NumWaveAsm, Chain!NumWaveAsm,NumProcessorAsm, Chain!NumProcessorAsm 

LEMMA Speccorrectness == Spec => Chain!Spec   
 <1>1 Init => Chain!Init
    BY DEF Init
 <1>2 ASSUME TypeOK, [Next]_vars 
      PROVE Chain!Next \/ UNCHANGED Chain!vars
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p,b)
           PROVE Chain!Next \/ UNCHANGED Chain!vars
           BY VertexSetDef,<2>1,<1>2 DEF  ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE Chain!Next \/ UNCHANGED Chain!vars
           <3>1 ASSUME NEW q \in ProcessorSet, NEW w \in WaveSet, ReadyWave(p,w)
                PROVE Chain!Next \/ UNCHANGED Chain!vars
                BY unchangedDef,<3>1,<1>2 DEF ReadyWave, TypeOK, Chain!Next
           <3>2 CASE DAGround[p]>0 /\ (DAGround[p] % 4) = 0
                <4>1 DAGround[p] \div 4 \in WaveSet
                     BY divprop2,<3>2,<1>2,<2>1,NumWaveAsm DEF TypeOK, WaveSet, RoundSet
                <4> QED BY <4>1,<3>2,<3>1,<2>2,<1>2 DEF NextRoundTn
           <3>3 CASE ~(DAGround[p]>0 /\ (DAGround[p] % 4) = 0)
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
                <4> QED BY <2>4,<3>1,<4>1,<4>2,unchangedDef DEF AddVertexTn, Chain!Next
           <3>2 CASE v.round % 4 # 1 \/ v.source # ChooseLeader((v.round \div 4)+1)
                BY <3>2,<2>4 DEF AddVertexTn
           <3> QED BY <3>1,<3>2, vertexType \*VertexSetDef,<2>4,<1>2 DEF AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY <2>5 DEF vars, Chain!vars
      <2> QED BY <1>2,<2>1,<2>2,<2>3,<2>4,<2>5 DEF Next 
 <1> QED BY <1>1,<1>2,PTL, Typecorrectness DEF Spec, Chain!Spec   

LEMMA SystemTypecorrectness == Spec => []TypeOK_System
  BY Typecorrectness, PTL, Chain!Typecorrectness, Speccorrectness,NumWaveAsm, NumProcessorAsm DEF TypeOK_System

LEMMA ChainConsistancycorrectness == Spec=> []ChainConsistancy  
  BY Chain!ChainConsistancycorrectness,Speccorrectness,NumWaveAsm, NumProcessorAsm, unchangedDef DEF Chain!ChainConsistancy, ChainConsistancy
LEMMA ChainMonotonicitycorrectness == Spec => []ChainMonotonicity
  BY Chain!ChainMonotonicitycorrectness,Speccorrectness,NumWaveAsm, NumProcessorAsm, unchangedDef DEF Chain!ChainMonotonicity, ChainMonotonicity

=============================================================================
\* Modification History
\* Last modified Mon Jan 15 13:50:10 AEDT 2024 by Pranav
\* Created Mon Jan 15 13:07:49 AEDT 2024 by Pranav
