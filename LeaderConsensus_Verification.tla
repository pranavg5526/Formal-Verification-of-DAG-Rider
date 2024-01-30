-------------------- MODULE LeaderConsensus_Verification --------------------
EXTENDS Integers, TLAPS, TLC, Sequences, LeaderConsensus_Spec, FiniteSets, SequenceOpTheorems

LEMMA maxIn == \A E \in SUBSET(WaveSet) : E # {} =>  max(E) \in E 
      
LEMMA maxProperty == \A E \in SUBSET(WaveSet) : \A x \in E: E # {} => x<=max(E)

LEMMA SelfIsPrefixLem == \A S \in Seq(WaveSet) : IsPrefix(S, S) = TRUE
      <1>1 \A S \in Seq(WaveSet) : S \o <<>> = S /\ <<>> \in Seq(WaveSet)
           OBVIOUS
      <1> QED BY IsPrefixConcat, <1>1
      
LEMMA TransitiveIsPrefixLem == ASSUME NEW S \in Seq(WaveSet), NEW L \in Seq(WaveSet), NEW M \in Seq(WaveSet), IsPrefix(S,L), IsPrefix(L,M)
                            PROVE IsPrefix(S,M)
      <1>1 \E u,w \in Seq(WaveSet) : L = S \o u /\ M = L \o w
           BY IsPrefixProperties
      <1>2 \A n,m, u \in Seq(WaveSet) : (n \o m) \o u = n \o (m \o u)
           OBVIOUS
      <1>3  \E u,w \in Seq(WaveSet) : M = S \o (u \o w)
           BY <1>1
      <1>4 \A u,w \in Seq(WaveSet) : u \o w \in Seq(WaveSet) 
           OBVIOUS
      <1>5 \A u,w \in Seq(WaveSet) : M = S \o (u \o w) /\ u \o w \in Seq(WaveSet) => IsPrefix(S,M)
           BY IsPrefixConcat
      <1> QED BY <1>5,<1>4,<1>3

LEMMA AppendIsPrefixLem == \A S \in Seq(WaveSet), w \in WaveSet : IsPrefix(S, Append(S,w))
      <1>1 \A S \in Seq(WaveSet), w \in WaveSet : <<w>> \in Seq(WaveSet) /\ Append(S,w) = S \o <<w>>
           OBVIOUS
      <1> QED BY <1>1, IsPrefixConcat
     
     
LEMMA TypeCorrectnessLem == Spec => []StateType
 <1>1 Init => StateType
      BY DEF Init, StateType
 <1>2 ASSUME StateType, Next
      PROVE StateType'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
           PROVE StateType'
           <3>1 leaderReachablity' \in [ProcessorSet -> [WaveSet -> [exists : BOOLEAN, edges : SUBSET(WaveSet)]]]
                BY  <2>1, <1>2 DEF ProcessorSet, WaveSet, StateType, UpdateWaveTn
           <3>2 commitWithRef' \in [ProcessorSet -> [WaveSet -> Seq(WaveSet)]]
                <4>1 <<w>> \in Seq(WaveSet)
                     BY <2>1 
                <4>2 E # {} =>max(E) \in WaveSet
                     BY maxIn,<2>1
                <4>3 E # {} => Append(commitWithRef[p][max(E)], w) \in Seq(WaveSet)
                     <5>1 E # {} => commitWithRef[p][max(E)] \in Seq(WaveSet)
                          BY <2>1, <4>2,<1>2 DEF StateType
                     <5> QED BY <5>1, <2>1 
                <4> QED BY  <4>1,<4>3, <2>1, <1>2 DEF StateType, UpdateWaveTn
           <3> QED BY <3>1,<3>2, <2>1,<1>2 DEF StateType, UpdateWaveTn
      <2>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
           PROVE StateType'
           <3>1 decidedWave' \in [ProcessorSet -> WaveSet \cup {0}]
                BY  <2>2, <1>2 DEF ProcessorSet, WaveSet, StateType, UpdateDecidedWaveTn
           <3>2 leaderSeq' \in [ProcessorSet -> [current : Seq(WaveSet), last : Seq(WaveSet)]]
                <4>1 commitWithRef[p][w] \in Seq(WaveSet) /\ leaderSeq[p].current \in Seq(WaveSet)
                     BY <2>2, <1>2 DEF StateType
                <4> QED BY  <4>1, <2>2, <1>2 DEF ProcessorSet, WaveSet, StateType, UpdateDecidedWaveTn
           <3> QED BY <3>1,<3>2, <2>2,<1>2 DEF StateType, UpdateDecidedWaveTn
      <2> QED BY <2>1,<2>2, <1>2 DEF Next
 <1>3 StateType /\ UNCHANGED vars => StateType'
      BY DEF vars, StateType
 <1> QED BY <1>1,<1>2,<1>3, PTL DEF Spec

LEMMA Invariant1CorrectnessLem == Spec => []Invariant1
 <1>1 Init => Invariant1
      BY DEF Init, Invariant1
 <1>2 StateType /\ StateType' /\ Invariant1 /\ [Next]_vars => Invariant1'
      <2>1 ASSUME StateType, StateType', Next, Invariant1
           PROVE Invariant1'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Invariant1'
                <4>1 ASSUME NEW q \in ProcessorSet, decidedWave'[q] # 0
                     PROVE leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                     <5>1 decidedWave'[q] \in WaveSet
                          BY <2>1, <4>1 DEF StateType
                     <5>2 CASE decidedWave'[q] = w /\ p = q 
                          BY <5>2,<3>1,<2>1 DEF StateType, UpdateWaveTn
                     <5>3 CASE decidedWave'[q] # w \/ p # q
                          <6>1 decidedWave[q] # 0
                               BY <3>1,<2>1,<4>1, <5>3 DEF StateType, UpdateWaveTn
                          <6>2 leaderReachablity'[q][decidedWave'[q]].exists = leaderReachablity[q][decidedWave[q]].exists
                               BY <5>3,<3>1,<2>1, <5>1, <4>1 DEF StateType, UpdateWaveTn
                          <6> QED BY <6>1,<6>2, <2>1 DEF Invariant1
                     <5> QED BY <5>3,<5>2
                <4> QED BY <4>1 DEF Invariant1
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Invariant1'
                <4>1 ASSUME NEW q \in ProcessorSet, decidedWave'[q] # 0
                     PROVE leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                     <5>1 decidedWave'[q] \in WaveSet
                          BY <2>1, <4>1 DEF StateType
                     <5>2 CASE  p = q 
                          BY <5>2,<3>2,<2>1 DEF StateType, UpdateDecidedWaveTn
                     <5>3 CASE p # q
                          <6>1 decidedWave[q] # 0
                               BY <3>2,<2>1,<4>1, <5>3 DEF StateType, UpdateDecidedWaveTn
                          <6>2 leaderReachablity'[q][decidedWave'[q]].exists = leaderReachablity[q][decidedWave[q]].exists
                               BY <5>3,<3>2,<2>1, <5>1, <4>1 DEF StateType, UpdateDecidedWaveTn
                          <6> QED BY <6>1,<6>2, <2>1 DEF Invariant1
                     <5> QED BY <5>3,<5>2
                <4> QED BY <4>1 DEF Invariant1
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Invariant1
           PROVE Invariant1'
           BY <2>2 DEF vars, Invariant1
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, PTL DEF Spec


LEMMA Invariant2CorrectnessLem == Spec => []Invariant2
 <1>1 Init => Invariant2
      BY DEF Init, Invariant2
 <1>2 StateType /\ StateType' /\ Invariant1 /\ Invariant1' /\ Invariant2 /\ [Next]_vars => Invariant2'
      <2>1 ASSUME StateType, StateType', Next, Invariant2, Invariant1, Invariant1'
           PROVE Invariant2'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Invariant2'
                <4>1 ASSUME NEW q \in ProcessorSet 
                     PROVE leaderSeq'[q].current = IF decidedWave'[q] = 0 THEN <<>> ELSE commitWithRef'[q][decidedWave'[q]]
                     <5>1 leaderSeq'[q].current = leaderSeq[q].current
                          BY <4>1, <3>1,<2>1 DEF StateType, UpdateWaveTn
                     <5>2 decidedWave'[q] = decidedWave[q]
                          BY <4>1, <3>1,<2>1 DEF StateType, UpdateWaveTn
                     <5>3 decidedWave'[q] # 0 => commitWithRef'[q][decidedWave'[q]] = commitWithRef[q][decidedWave[q]]
                          <6>1 CASE q = p
                               <7>1 decidedWave[q] # 0 => leaderReachablity[q][decidedWave[q]].exists = TRUE
                                    BY <4>1, <2>1 DEF Invariant1
                               <7>2 decidedWave[q] # 0 => w # decidedWave[q]
                                    BY <7>1,<3>1, <6>1  DEF UpdateWaveTn
                               <7> QED BY <7>2, <4>1, <3>1, <2>1 DEF StateType, UpdateWaveTn
                          <6>2 CASE q # p
                               BY <6>2,<5>2,<3>1,<4>1,<2>1 DEF StateType, UpdateWaveTn
                          <6> QED BY <6>1,<6>2
                     <5> QED BY <5>1,<5>2,<5>3, <2>1 DEF Invariant2
                <4> QED BY <4>1 DEF Invariant2  
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Invariant2'
                <4>1 ASSUME NEW q \in ProcessorSet 
                     PROVE leaderSeq'[q].current = IF decidedWave'[q] = 0 THEN <<>> ELSE commitWithRef'[q][decidedWave'[q]]
                     <5>1 CASE p = q
                          <6>1 decidedWave'[q] = w
                               BY <5>1, <3>2,<2>1 DEF StateType, UpdateDecidedWaveTn
                          <6>2 leaderSeq'[q].current = commitWithRef'[q][decidedWave'[q]]
                               BY <5>1, <3>2,<2>1, <6>1 DEF StateType, UpdateDecidedWaveTn
                          <6> QED BY <6>1, <6>2, <3>1 DEF WaveSet
                     <5>2 CASE p # q
                          <6>1 leaderSeq'[q].current =leaderSeq[q].current
                               BY <4>1, <5>2, <3>2,<2>1 DEF StateType, UpdateDecidedWaveTn
                          <6>2 decidedWave'[q] = decidedWave[q]
                               BY <4>1, <5>2, <3>2,<2>1 DEF StateType, UpdateDecidedWaveTn
                          <6>3 decidedWave'[q] # 0 => commitWithRef'[q][decidedWave'[q]] = commitWithRef[q][decidedWave[q]]
                               BY <5>2,<6>2,<3>2,<4>1,<2>1 DEF StateType, UpdateDecidedWaveTn
                          <6> QED BY <6>1,<6>2,<6>3, <2>1 DEF Invariant2
                     <5> QED BY <5>1,<5>2
                <4> QED BY <4>1 DEF Invariant2  
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Invariant2
           PROVE Invariant2'
           BY <2>2 DEF vars, Invariant2
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, Invariant1CorrectnessLem, PTL DEF Spec
 
  
LEMMA Invariant3CorrectnessLem == Spec => []Invariant3
 <1>1 Init => Invariant3
      BY DEF Init, Invariant3
 <1>2 StateType /\ StateType' /\ Invariant3 /\ [Next]_vars => Invariant3'
      <2>1 ASSUME StateType, StateType', Next, Invariant3
           PROVE Invariant3'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Invariant3'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in leaderReachablity'[q][x].edges
                     PROVE leaderReachablity'[q][y].exists = TRUE
                     <5>1 y \in WaveSet
                          BY <4>1, <2>1 DEF StateType
                     <5>2 CASE q = p /\ x = w
                          BY <5>2,<3>1,<2>1,<4>1 DEF StateType, UpdateWaveTn
                     <5>3 CASE q # p \/ x # w
                          <6>1 leaderReachablity'[q][x].edges = leaderReachablity[q][x].edges
                               BY <5>3,<4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                          <6>2 leaderReachablity[q][y].exists = leaderReachablity'[q][y].exists
                               <7>1 w # y \/ q # p
                                    <8>1 leaderReachablity[q][y].exists = TRUE
                                         BY <6>1, <4>1,<2>1 DEF Invariant3
                                    <8> QED BY <8>1, <3>1, <4>1 DEF UpdateWaveTn
                               <7> QED BY <7>1,<5>1,<4>1,<3>1, <2>1 DEF StateType, UpdateWaveTn
                          <6> QED BY <6>1,<6>2,<4>1,<2>1 DEF Invariant3, StateType
                     <5> QED  BY <5>2,<5>3 
                <4> QED BY <4>1 DEF Invariant3
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Invariant3'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in leaderReachablity'[q][x].edges
                     PROVE leaderReachablity'[q][y].exists = TRUE 
                     <5>1 leaderReachablity'[q][x].edges = leaderReachablity[q][x].edges 
                          BY <4>1,<3>2,<2>1 DEF StateType, UpdateDecidedWaveTn
                     <5>2 leaderReachablity'[q][y].exists = leaderReachablity[q][y].exists
                          BY <4>1,<3>2,<2>1 DEF StateType, UpdateDecidedWaveTn
                     <5> QED BY <5>1,<5>2,<4>1, <2>1 DEF Invariant3
                <4> QED BY <4>1 DEF Invariant3
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Invariant3
           PROVE Invariant3'
           BY <2>2 DEF vars, Invariant3
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, PTL DEF Spec      


LEMMA Invariant4CorrectnessLem == Spec => []Invariant4
 <1>1 Init => Invariant4
      BY DEF Init, Invariant4, Contains
 <1>2 StateType /\ StateType' /\ Invariant4 /\ [Next]_vars => Invariant4'
      <2>1 ASSUME StateType, StateType', Next, Invariant4
           PROVE Invariant4'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Invariant4'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y])
                     PROVE leaderReachablity'[q][x].exists = TRUE
                     <5>1 CASE p = q
                          <6>1 CASE x = w
                               BY <6>1,<5>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                          <6>2 CASE x # w
                               <7>1 CASE y # w
                                    BY <7>1,<6>2,<4>1,<3>1,<2>1 DEF StateType, Invariant4, UpdateWaveTn
                               <7>2 CASE y = w
                                    <8>1 E # {}
                                         BY <6>2,<4>1,<3>1, <7>2,<5>1,<2>1 DEF StateType, UpdateWaveTn, Contains
                                    <8>2 Contains(x, commitWithRef[q][max(E)])
                                         BY <6>2,<4>1,<3>1, <7>2,<5>1,<2>1, <8>1 DEF StateType, UpdateWaveTn, Contains
                                    <8>3 leaderReachablity'[q][x].exists = leaderReachablity[q][x].exists
                                         BY <6>2,<4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                                    <8> QED BY <8>2,<8>1, <8>3, maxIn, <4>1, <2>1, <3>1 DEF Invariant4
                               <7> QED BY <7>1,<7>2
                          <6> QED BY <6>1, <6>2
                     <5>2 CASE p # q
                          BY <5>2,<4>1,<3>1,<2>1 DEF StateType, Invariant4, UpdateWaveTn
                     <5> QED BY <5>1,<5>2 
                <4> QED BY <4>1 DEF Invariant4
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Invariant4'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y])
                     PROVE leaderReachablity'[q][x].exists = TRUE
                     BY <4>1,<3>2,<2>1 DEF StateType, Invariant4, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF Invariant4
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Invariant4
           PROVE Invariant4'
           BY <2>2 DEF vars, Invariant4
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, PTL DEF Spec
 
 
LEMMA Invariant5CorrectnessLem == Spec => []Invariant5
 <1>1 Init => Invariant5
      BY DEF Init, Invariant5, Contains
 <1>2 StateType /\ StateType' /\ Invariant5 /\ [Next]_vars /\ Invariant4 /\ Invariant4' => Invariant5'
      <2>1 ASSUME StateType, StateType', Next, Invariant5, Invariant4, Invariant4'
           PROVE Invariant5'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Invariant5'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y])
                     PROVE IsPrefix(commitWithRef'[q][x], commitWithRef'[q][y])
                     <5>1 CASE p = q
                          <6>1 CASE x = w
                               <7>1 CASE y = w
                                    BY <7>1,<6>1, <4>1, <2>1, SelfIsPrefixLem DEF StateType
                               <7>2 CASE y # w
                                    <8>1 leaderReachablity[q][x].exists = TRUE
                                         <9>1 Contains(x, commitWithRef[q][y])
                                              <10>1 commitWithRef'[q][y] = commitWithRef[q][y]
                                                    BY <7>2,<4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                                              <10> QED BY <4>1,<10>1
                                         <9> QED BY <9>1,<4>1,<2>1 DEF Invariant4
                                    <8>2 leaderReachablity[q][x].exists = FALSE
                                         BY <6>1,<5>1,<3>1 DEF UpdateWaveTn
                                    <8> QED BY <8>1,<8>2
                               <7> QED BY <7>1,<7>2
                          <6>2 CASE x # w
                               <7>1 CASE y # w
                                    BY <7>1,<6>2,<4>1,<3>1,<2>1 DEF StateType, Invariant5, UpdateWaveTn
                               <7>2 CASE y = w
                                    <8>1 E # {} /\ Contains(x, commitWithRef[q][max(E)])
                                         BY <5>1,<7>2,<6>2,<4>1,<3>1,<2>1 DEF Contains,StateType, UpdateWaveTn
                                    <8>2 max(E) \in WaveSet
                                         BY <8>1,<3>1,maxIn
                                    <8>3 commitWithRef'[q][x] = commitWithRef[q][x]
                                         BY <6>2,<3>1,<4>1,<2>1 DEF StateType, UpdateWaveTn
                                    <8>4 IsPrefix(commitWithRef'[q][x], commitWithRef[q][max(E)])
                                         BY <8>1,<8>2,<8>3,<4>1,<2>1 DEF StateType, Invariant5
                                    <8>5 IsPrefix(commitWithRef[q][max(E)], commitWithRef'[q][y])
                                         BY <8>1,<5>1,<7>2,<2>1,<3>1, AppendIsPrefixLem DEF StateType, UpdateWaveTn
                                    <8> QED BY <8>2,<8>4,<8>5,TransitiveIsPrefixLem,<4>1,<2>1 DEF StateType
                               <7> QED BY <7>1, <7>2
                          <6> QED BY <6>1,<6>2
                     <5>2 CASE p # q
                          BY <5>2,<4>1,<3>1,<2>1 DEF StateType, Invariant5, UpdateWaveTn
                     <5> QED BY <5>1,<5>2 
                <4> QED BY <4>1 DEF Invariant5
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Invariant5'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y])
                     PROVE IsPrefix(commitWithRef'[q][x], commitWithRef'[q][y])
                     BY <4>1,<3>2,<2>1 DEF StateType, Invariant5, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF Invariant5
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Invariant5
           PROVE Invariant5'
           BY <2>2 DEF vars, Invariant5
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, Invariant4CorrectnessLem, PTL DEF Spec

\*\A p \in ProcessorSet, w \in WaveSet: leaderReachablity[p][w].exists = TRUE => commitWithRef[p][w] = IF leaderReachablity[p][w].edges = {} THEN <<w>> ELSE Append(commitWithRef[p][max(leaderReachablity[p][w].edges)], w) 

LEMMA Invariant6CorrectnessLem == Spec => []Invariant6
 <1>1 Init => Invariant6
      BY DEF Init, Invariant6
 <1>2 StateType /\ StateType' /\ Invariant6 /\ [Next]_vars /\ Invariant3 /\ Invariant3' => Invariant6'
      <2>1 ASSUME StateType, StateType', Next, Invariant6, Invariant3, Invariant3'
           PROVE Invariant6'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Invariant6'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = TRUE
                     PROVE commitWithRef'[q][x] = IF leaderReachablity'[q][x].edges = {} THEN <<x>> ELSE Append(commitWithRef'[q][max(leaderReachablity'[q][x].edges)], x)
                     <5>1 CASE q = p /\ x = w
                          <6>1 leaderReachablity'[q][x].edges = E
                               BY <5>1,<3>1,<2>1 DEF UpdateWaveTn, StateType
                          <6>3 E # {} => commitWithRef'[q][max(E)] = commitWithRef[q][max(E)]
                               <7>1 E # {} => w # max(E)
                                    BY maxIn, <3>1 DEF UpdateWaveTn
                               <7> QED BY <7>1,<4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                          <6> QED BY <6>1, <5>1,<4>1,<3>1,<2>1,<6>3 DEF StateType, UpdateWaveTn
                     <5>2 CASE q # p \/ x # w
                          <6>1 commitWithRef'[q][x] = commitWithRef[q][x] 
                               BY <5>2,<4>1,<3>1,<2>1 DEF StateType,UpdateWaveTn
                          <6>2 leaderReachablity'[q][x].edges = leaderReachablity[q][x].edges /\ leaderReachablity'[q][x].exists = leaderReachablity[q][x].exists
                               BY <5>2,<4>1,<3>1,<2>1 DEF StateType,UpdateWaveTn
                          <6>3 leaderReachablity'[q][x].edges # {} => commitWithRef'[q][max(leaderReachablity'[q][x].edges)] = commitWithRef[q][max(leaderReachablity[q][x].edges)]
                               <7>1 leaderReachablity[q][x].edges # {} => max(leaderReachablity[q][x].edges) # w \/ q # p
                                    <8>1 leaderReachablity[q][x].edges # {} => leaderReachablity[q][max(leaderReachablity[q][x].edges)].exists = TRUE
                                         <9>1 leaderReachablity[q][x].edges \in SUBSET(WaveSet)
                                              BY <4>1,<2>1 DEF StateType
                                         <9>2 leaderReachablity[q][x].edges # {} => max(leaderReachablity[q][x].edges) \in leaderReachablity[q][x].edges
                                              BY <4>1,<2>1,<9>1, maxIn DEF StateType
                                         <9> QED BY <2>1,<4>1,<3>1,<9>2 DEF StateType, Invariant3
                                    <8> QED BY <8>1,<3>1,<4>1,<2>1, maxIn DEF StateType, UpdateWaveTn
                               <7> QED BY <7>1,<4>1,<3>1,<2>1, <6>2 DEF StateType, UpdateWaveTn
                          <6> QED BY <6>1,<6>2,<6>3,<4>1,<2>1 DEF Invariant6
                     <5> QED BY <5>1,<5>2
                <4> QED BY <4>1 DEF Invariant6
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Invariant6'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = TRUE
                     PROVE commitWithRef'[q][x] = IF leaderReachablity'[q][x].edges = {} THEN <<x>> ELSE Append(commitWithRef'[q][max(leaderReachablity'[q][x].edges)], x)
                     BY <4>1,<3>2,<2>1 DEF StateType, Invariant6, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF Invariant6
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Invariant6
           PROVE Invariant6'
           BY <2>2 DEF vars, Invariant6
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, Invariant3CorrectnessLem, PTL DEF Spec
 

LEMMA Invariant7CorrectnessLem == Spec => []Invariant7
 <1>1 Init => Invariant7
      BY DEF Init, Invariant7
 <1>2 StateType /\ StateType' /\ Invariant7 /\ [Next]_vars /\ Invariant6 /\ Invariant3 => Invariant7'
      <2>1 ASSUME StateType, StateType', Next, Invariant7, Invariant6, Invariant3
           PROVE Invariant7'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Invariant7'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = leaderReachablity'[r][x].exists
                     PROVE commitWithRef'[q][x] = commitWithRef'[r][x]
                     <5>1 CASE q = r
                          BY <5>1
                     <5>2 CASE q # r
                          <6>1 CASE x # w
                               BY <6>1,<4>1,<3>1,<2>1 DEF UpdateWaveTn,StateType,Invariant7
                          <6>2 CASE x = w
                               <7>1 CASE q = p
                                    <8>1 leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists /\ commitWithRef[r][x] = commitWithRef'[r][x]
                                         BY <7>1,<5>2,<4>1,<3>1,<2>1 DEF UpdateWaveTn,StateType
                                    <8>2 leaderReachablity'[q][x].exists /\ leaderReachablity'[r][x].exists
                                         BY <7>1,<6>2,<4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                                    <8>3 commitWithRef[r][x] = IF leaderReachablity[r][x].edges = {} THEN <<x>> ELSE Append(commitWithRef[r][max(leaderReachablity[r][x].edges)], x)
                                         BY <8>1,<4>1,<2>1,<8>2 DEF Invariant6
                                    <8>4 E  = leaderReachablity[r][x].edges
                                         BY <6>2,<4>1,<3>1,<8>1,<8>2 DEF UpdateWaveTn
                                    <8>5 commitWithRef'[q][x] = IF E = {} THEN <<x>> ELSE Append(commitWithRef[q][max(E)], x)
                                         BY <7>1,<6>2,<3>1,<2>1 DEF StateType, UpdateWaveTn
                                    <8>7 E # {} => leaderReachablity[r][max(E)].exists /\ leaderReachablity[q][max(E)].exists
                                         BY <8>4, maxIn,<3>1,<4>1,<2>1,<7>1 DEF Invariant3, UpdateWaveTn
                                    <8>6 E # {} => commitWithRef[q][max(E)] = commitWithRef[r][max(E)]
                                         BY <4>1,<3>1,maxIn,<2>1,<8>7 DEF Invariant7
                                    <8> QED BY <8>3,<8>4,<8>5,<8>6,<8>1
                               <7>2 CASE r = p
                                    <8>1 leaderReachablity'[q][x].exists = leaderReachablity[q][x].exists /\ commitWithRef[q][x] = commitWithRef'[q][x]
                                         BY <7>2,<5>2,<4>1,<3>1,<2>1 DEF UpdateWaveTn,StateType
                                    <8>2 leaderReachablity'[r][x].exists /\ leaderReachablity'[q][x].exists
                                         BY <7>2,<6>2,<4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                                    <8>3 commitWithRef[q][x] = IF leaderReachablity[q][x].edges = {} THEN <<x>> ELSE Append(commitWithRef[q][max(leaderReachablity[q][x].edges)], x)
                                         BY <8>1,<4>1,<2>1,<8>2 DEF Invariant6
                                    <8>4 E  = leaderReachablity[q][x].edges
                                         BY <6>2,<4>1,<3>1,<8>1,<8>2 DEF UpdateWaveTn
                                    <8>5 commitWithRef'[r][x] = IF E = {} THEN <<x>> ELSE Append(commitWithRef[r][max(E)], x)
                                         BY <7>2,<6>2,<3>1,<2>1 DEF StateType, UpdateWaveTn
                                    <8>7 E # {} => leaderReachablity[q][max(E)].exists /\ leaderReachablity[r][max(E)].exists
                                         BY <8>4, maxIn,<3>1,<4>1,<2>1,<7>2 DEF Invariant3, UpdateWaveTn
                                    <8>6 E # {} => commitWithRef[r][max(E)] = commitWithRef[q][max(E)]
                                         BY <4>1,<3>1,maxIn,<2>1,<8>7 DEF Invariant7
                                    <8> QED BY <8>3,<8>4,<8>5,<8>6,<8>1     
                               <7>3 CASE q # p /\ r # p
                                    BY <7>3,<4>1,<3>1,<2>1 DEF UpdateWaveTn,StateType,Invariant7
                               <7> QED BY <7>1,<7>2,<7>3
                          <6> QED BY <6>1,<6>2
                     <5> QED BY <5>1,<5>2
                <4> QED BY <4>1 DEF Invariant7
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Invariant7'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = leaderReachablity'[r][x].exists
                     PROVE commitWithRef'[q][x] = commitWithRef'[r][x]
                     BY <4>1,<3>2,<2>1 DEF StateType, Invariant7, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF Invariant7
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Invariant7
           PROVE Invariant7'
           BY <2>2 DEF vars, Invariant7
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, Invariant3CorrectnessLem, Invariant6CorrectnessLem, PTL DEF Spec


LEMMA Invariant8CorrectnessLem == Spec => []Invariant8
 <1>1 Init => Invariant8
      BY DEF Init, Invariant8
 <1>2 StateType /\ StateType' /\ Invariant8 /\ [Next]_vars /\ Invariant6' => Invariant8'
      <2>1 ASSUME StateType, StateType', Next, Invariant8, Invariant6'
           PROVE Invariant8'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Invariant8'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW z \in WaveSet, z >= x, leaderReachablity'[q][z].exists, \A y \in WaveSet : y > x /\ leaderReachablity'[q][y].exists => x \in leaderReachablity'[q][y].edges
                     PROVE Contains(x, commitWithRef'[q][z]) 
                     <5>1 CASE x = z
                          <6>1 commitWithRef'[q][z] = IF leaderReachablity'[q][z].edges # {} THEN Append(commitWithRef'[q][max(leaderReachablity'[q][z].edges)], z) ELSE <<z>>
                               BY  <2>1,<4>1 DEF Invariant6
                          <6>2 leaderReachablity'[q][z].edges # {} => Contains(z, commitWithRef'[q][z]) 
                               BY <6>1 DEF Contains
                          <6> QED BY <5>1 ,<6>1,<6>2 DEF Contains
                     <5>2 CASE x # z
                          <6>1 z > x
                               BY <5>2,<4>1
                          <6>2 \A y \in WaveSet : y > x /\ leaderReachablity[q][y].exists => x \in leaderReachablity[q][y].edges
                               <7>1 \A y \in WaveSet : y > x /\ (y # w \/ q # p) /\ leaderReachablity[q][y].exists => x \in leaderReachablity[q][y].edges
                                    BY <4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                               <7>2 \A y \in WaveSet : y > x /\ (y = w /\ q = p) => leaderReachablity[q][y].exists = FALSE
                                    BY <4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                               <7> QED BY <7>1,<7>2
                          <6>3 CASE p = q /\ w = z
                               <7>1 leaderReachablity'[q][z].edges = E
                                    BY <2>1,<6>3,<3>1 DEF UpdateWaveTn, StateType
                               <7>2 x \in E
                                    BY <6>1,<4>1,<7>1
                               <7>3 commitWithRef'[q][z] = Append(commitWithRef'[q][max(E)], z)
                                    BY  <2>1,<4>1,<7>1,<7>2 DEF Invariant6
                               <7>4 max(E) # w /\ max(E) >= x
                                    BY <7>2,maxIn,<3>1, maxProperty DEF UpdateWaveTn
                               <7>5 leaderReachablity[q][max(E)].exists
                                    BY <6>3,<3>1,<7>2,maxIn DEF UpdateWaveTn
                               <7>6 commitWithRef'[q][max(E)] = commitWithRef[q][max(E)]
                                    BY <7>4,<3>1,<6>3,<2>1 DEF StateType, UpdateWaveTn
                               <7>7 Contains(x, commitWithRef[q][max(E)])
                                    BY <7>6,<7>5,<6>2,<7>4,<7>2,<3>1,<2>1,<4>1, maxIn DEF Invariant8
                               <7> QED BY <7>7,<7>6,<7>3 DEF Contains
                          <6>4 CASE p # q \/ w # z
                               BY <6>2,<4>1,<6>4,<3>1,<2>1 DEF StateType, UpdateWaveTn, Invariant8
                          <6> QED BY <6>3,<6>4
                     <5> QED BY <5>1,<5>2
                <4> QED BY <4>1 DEF Invariant8
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Invariant8'
                BY <3>2,<2>1 DEF StateType, Invariant8, UpdateDecidedWaveTn
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Invariant8
           PROVE Invariant8'
           BY <2>2 DEF vars, Invariant8
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, Invariant6CorrectnessLem, PTL DEF Spec


LEMMA Invariant9CorrectnessLem == Spec => []Invariant9
 <1>1 Init => Invariant9
      BY DEF Init, Invariant9
 <1>2 StateType /\ StateType' /\ Invariant9 /\ [Next]_vars /\ Invariant8 /\ Invariant6 /\ Invariant3 => Invariant9'
      <2>1 ASSUME StateType, StateType', Next, Invariant8, Invariant6, Invariant3, Invariant9
           PROVE Invariant9'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Invariant9'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, decidedWave'[q] # 0, x >= decidedWave'[q], leaderReachablity'[r][x].exists = TRUE
                     PROVE Contains(decidedWave'[q], commitWithRef'[r][x])
                     <5>1 decidedWave'[q] = decidedWave[q]
                          BY <4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                     <5>2 CASE x # w
                          <6>1 commitWithRef'[r][x] = commitWithRef[r][x] /\ leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists
                               BY <5>2,<4>1,<3>1,<2>1 DEF StateType,UpdateWaveTn
                          <6> QED BY <6>1,<5>1,<4>1,<2>1 DEF Invariant9
                     <5>3 CASE x = w
                          <6>1 CASE r = p
                               <7>1 E # {} => commitWithRef'[r][x] = Append(commitWithRef[r][max(E)], x)
                                    BY <3>1,<2>1,<6>1,<5>3 DEF UpdateWaveTn, StateType
                               <7>2 CASE decidedWave'[q] = x 
                                    <8>1 Contains(x, commitWithRef'[r][x])
                                         BY <7>1,<3>1,<2>1,<5>3,<6>1 DEF Contains,UpdateWaveTn, StateType
                                    <8> QED BY <8>1,<7>2
                               <7>3 CASE decidedWave'[q] # x 
                                    <8>1 decidedWave'[q] \in E /\ E # {}
                                         <9>1 decidedWave'[q] < x
                                              BY <7>3,<4>1
                                         <9> QED BY <9>1,<5>3,<4>1,<3>1 DEF UpdateWaveTn
                                    <8>2 Contains(decidedWave'[q], commitWithRef[r][max(E)])
                                         <9>1 max(E) \in E
                                              BY <8>1,<3>1,maxIn
                                         <9>2 decidedWave'[q] =< max(E)
                                              BY <8>1, maxProperty,<3>1 DEF max
                                         <9>3 leaderReachablity[r][max(E)].exists = TRUE
                                              BY <8>1,<6>1,<3>1,<9>1 DEF UpdateWaveTn
                                         <9> QED BY <9>1,<4>1,<9>2,<9>3,<2>1,<5>1 DEF Invariant9, StateType
                                    <8> QED BY <8>1,<7>1,<8>2 DEF Contains
                               <7> QED BY <7>2,<7>3
                          <6>2 CASE r # p
                               <7>1 commitWithRef'[r][x] = commitWithRef[r][x] /\ leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists
                                    BY <6>2,<4>1,<3>1,<2>1 DEF StateType, UpdateWaveTn
                               <7> QED BY <7>1,<5>1,<4>1,<2>1 DEF Invariant9
                          <6> QED BY <6>1,<6>2
                     <5> QED BY <5>2,<5>3
                <4> QED BY <4>1 DEF Invariant9
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Invariant9'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, decidedWave'[q] # 0, x >= decidedWave'[q], leaderReachablity'[r][x].exists = TRUE
                     PROVE Contains(decidedWave'[q], commitWithRef'[r][x])
                     <5>1 commitWithRef'[r][x] = commitWithRef[r][x] /\ leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists
                          BY <4>1,<3>2,<2>1 DEF StateType,UpdateDecidedWaveTn
                     <5>2 CASE q # p
                          <6>1 decidedWave'[q] = decidedWave[q]
                               BY <5>2,<4>1,<3>2,<2>1 DEF StateType,UpdateDecidedWaveTn
                          <6> QED BY <6>1,<5>1,<2>1,<4>1 DEF Invariant9
                     <5>3 CASE q = p
                          <6>1 decidedWave'[q] = w
                               BY <5>3,<3>2,<2>1 DEF StateType, UpdateDecidedWaveTn
                          <6>2 commitWithRef[r][x] = IF leaderReachablity[r][x].edges # {} THEN Append(commitWithRef[r][max(leaderReachablity[r][x].edges)], x) ELSE <<x>>
                               BY <4>1,<2>1,<5>1 DEF Invariant6
                          <6>3 CASE q = r
                               <7>1 CASE x = w
                                    <8>1 Contains(x, commitWithRef[r][x])
                                         <9>1 CASE leaderReachablity[r][x].edges # {}
                                             BY <9>1,<6>2 DEF Contains
                                         <9>2 CASE leaderReachablity[r][x].edges = {} 
                                             BY <9>2,<6>2 DEF Contains
                                         <9> QED BY <9>1,<9>2
                                    <8> QED BY <8>1,<7>1,<6>1,<5>1
                               <7>2 CASE x # w
                                    <8>1 x > w
                                         BY <7>2,<6>1,<4>1
                                    <8>2 leaderReachablity[r][x].exists = FALSE
                                         BY <8>1,<6>3,<5>3,<3>2,<2>1,<4>1 DEF StateType, UpdateDecidedWaveTn
                                    <8> QED BY <8>2,<5>1,<4>1
                              <7> QED BY <7>1,<7>2
                          <6>4 CASE q # r
                              <7>1 CASE x = w
                                   <8>1 Contains(x, commitWithRef[r][x])
                                         <9>1 CASE leaderReachablity[r][x].edges # {}
                                             BY <9>1,<6>2 DEF Contains
                                         <9>2 CASE leaderReachablity[r][x].edges = {} 
                                             BY <9>2,<6>2 DEF Contains
                                         <9> QED BY <9>1,<9>2
                                   <8> QED BY <8>1,<7>1,<6>1,<5>1
                              <7>2 CASE x # w
                                   <8>1 w \in leaderReachablity[r][x].edges /\ leaderReachablity[r][x].edges # {}
                                        <9>1 w < x
                                             BY <7>2,<4>1,<6>1
                                        <9> QED BY <9>1,<5>3,<4>1,<3>2,<6>2,<4>1 DEF UpdateDecidedWaveTn
                                   <8>2 leaderReachablity[r][x].edges \in SUBSET(WaveSet)
                                        BY <4>1,<2>1 DEF StateType
                                   <8>3 Contains(w, commitWithRef[r][max(leaderReachablity[r][x].edges)])     
                                        <9>1 max(leaderReachablity[r][x].edges) \in leaderReachablity[r][x].edges
                                             BY <8>1,<4>1,maxIn, <8>2
                                        <9>2 w =< max(leaderReachablity[r][x].edges)
                                             BY <8>1, maxProperty,<3>1,<8>2 DEF max
                                        <9>3 leaderReachablity[r][max(leaderReachablity[r][x].edges)].exists = TRUE
                                             BY <4>1,<2>1,<9>1 DEF Invariant3
                                        <9>4 \A z \in WaveSet : z >= w /\ leaderReachablity[r][z].exists = TRUE => Contains(w,commitWithRef[r][z])
                                             BY <4>1,<3>2,<2>1 DEF Invariant8, UpdateDecidedWaveTn
                                        <9> QED BY <9>1,<9>2,<9>3,<9>4,<8>2
                                   <8>4 Contains(w, commitWithRef[r][max(leaderReachablity[r][x].edges)])  => Contains(w, Append(commitWithRef[r][max(leaderReachablity[r][x].edges)], x))
                                        BY DEF Contains
                                   <8> QED BY <8>1,<8>4, <6>2, <8>3,<6>1,<5>1 DEF Contains 
                              <7> QED BY <7>1,<7>2
                          <6> QED BY <6>3,<6>4
                     <5> QED BY <5>2,<5>3
                <4> QED BY <4>1 DEF Invariant9
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Invariant9
           PROVE Invariant9'
           BY <2>2 DEF vars, Invariant9
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem,Invariant8CorrectnessLem,Invariant6CorrectnessLem,Invariant3CorrectnessLem, PTL DEF Spec

LEMMA Invariant10CorrectnessLem == Spec => []Invariant10
 <1>1 Init => Invariant10
    BY DEF Init, Invariant10
 <1>2 Invariant1 /\ Invariant1' /\ Invariant4 /\ Invariant4' /\ Invariant7 /\ Invariant7' /\ Invariant5 /\ Invariant5'/\ Invariant9 /\ Invariant9' /\ StateType /\ StateType' /\ Invariant10 /\ [Next]_vars => Invariant10'
      <2>1 ASSUME Invariant9, Invariant9', StateType, StateType', Invariant10, [Next]_vars, Invariant1, Invariant1', Invariant4, Invariant4', Invariant7, Invariant7', Invariant5, Invariant5'
           PROVE Invariant10'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW w \in WaveSet, leaderReachablity'[p][w].exists = TRUE, w >= decidedWave'[q], decidedWave'[q] # 0
                PROVE IsPrefix(commitWithRef'[q][decidedWave'[q]], commitWithRef'[p][w])
                <4>1 Contains(decidedWave'[q], commitWithRef'[p][w]) 
                     BY <3>1,<2>1 DEF Invariant9
                <4>2 decidedWave'[q] \in WaveSet
                     BY <3>1, <2>1 DEF StateType
                <4>3 commitWithRef'[p][decidedWave'[q]] = commitWithRef'[q][decidedWave'[q]]
                     <5>1 leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                          BY <3>1, <2>1 DEF Invariant1    
                     <5>2 leaderReachablity'[p][decidedWave'[q]].exists = TRUE
                          BY <3>1,<4>1,<4>2, <2>1 DEF Invariant4
                     <5> QED BY <5>1, <5>2, <4>2, <3>1, <2>1 DEF Invariant7
                <4>4 IsPrefix(commitWithRef'[p][decidedWave'[q]], commitWithRef'[p][w])
                     BY <4>1,<4>2, <3>1, <2>1 DEF Invariant5
                <4> QED BY <4>3,<4>4
           <3> QED BY <3>1 DEF Invariant10
      <2> QED BY <2>1     
 <1> QED BY <1>1,<1>2, PTL, TypeCorrectnessLem, Invariant1CorrectnessLem, Invariant4CorrectnessLem,Invariant7CorrectnessLem,Invariant5CorrectnessLem, Invariant9CorrectnessLem DEF Spec             
 
THEOREM ChainConsistancyCorrectnessThm == Spec => []ChainConsistancy
 <1>1 Init => ChainConsistancy
      BY SelfIsPrefixLem DEF Init, ChainConsistancy
 <1>2 StateType /\ StateType' /\ Invariant10 /\ Invariant10' /\ Invariant1 /\ Invariant1'/\ Invariant2 /\ Invariant2' /\ [Next]_vars /\ ChainConsistancy => ChainConsistancy'
      <2>1 ASSUME StateType, StateType', Invariant10, Invariant10', [Next]_vars, ChainConsistancy, Invariant1, Invariant1', Invariant2, Invariant2'
           PROVE ChainConsistancy'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, decidedWave'[p] <= decidedWave'[q]
                PROVE IsPrefix(leaderSeq'[p].current, leaderSeq'[q].current)
                <4>1 CASE decidedWave'[p] = 0 /\ decidedWave'[q] = 0
                     <5>1 leaderSeq'[p].current = <<>> /\ leaderSeq'[q].current = <<>>
                          BY <4>1, <2>1, <3>1 DEF Invariant2
                     <5> QED BY <5>1, SelfIsPrefixLem
                <4>2 CASE decidedWave'[p] = 0 /\ decidedWave'[q] # 0
                     <5>1 leaderSeq'[p].current = <<>>
                          BY <4>2, <2>1, <3>1 DEF Invariant2
                     <5> QED BY <5>1, <2>1, EmptyIsPrefix DEF StateType
                <4>3 CASE decidedWave'[p] # 0 /\ decidedWave'[q] # 0
                     <5>1 leaderSeq'[p].current = commitWithRef'[p][decidedWave'[p]] /\ leaderSeq'[q].current = commitWithRef'[q][decidedWave'[q]]
                          BY <4>3, <2>1, <3>1 DEF Invariant2
                     <5>2 decidedWave'[q] \in WaveSet
                          BY <2>1, <4>3 DEF StateType
                     <5>3 leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                          BY <2>1, <3>1, <4>3 DEF Invariant1
                     <5> QED BY <5>1, <5>2,<5>3, <2>1, <3>1, <4>3 DEF Invariant10
                <4> QED BY <3>1, <4>1,<4>2,<4>3, <2>1 DEF StateType, WaveSet
           <3> QED BY <3>1 DEF ChainConsistancy
      <2> QED BY <2>1
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, Invariant10CorrectnessLem, Invariant1CorrectnessLem,Invariant2CorrectnessLem, PTL DEF Spec
 
THEOREM ChainMonotonicityCorrectnessThm == Spec => []ChainMonotonicity
 <1>1 Init => ChainMonotonicity
      BY SelfIsPrefixLem DEF Init, ChainMonotonicity
 <1>2 StateType /\ StateType' /\ Invariant10 /\ Invariant10' /\ Invariant1 /\ Invariant1'/\ Invariant2 /\ Invariant2' /\ [Next]_vars /\ ChainMonotonicity => ChainMonotonicity'
      <2>1 ASSUME StateType, StateType', Invariant10, Invariant10', Next, ChainMonotonicity,  Invariant1, Invariant1', Invariant2, Invariant2'
           PROVE ChainMonotonicity'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE ChainMonotonicity'
                BY <3>1,<2>1 DEF ChainMonotonicity, UpdateWaveTn
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE ChainMonotonicity'
                <4>1 ASSUME NEW q \in ProcessorSet
                     PROVE IsPrefix(leaderSeq'[q].last, leaderSeq'[q].current)
                     <5>1 CASE p = q
                          <6>1 leaderSeq'[q].current = commitWithRef[q][w]
                               BY <5>1,<3>2, <2>1 DEF UpdateDecidedWaveTn, StateType
                          <6>2 leaderSeq'[q].last = leaderSeq[q].current
                               BY <5>1,<3>2, <2>1 DEF UpdateDecidedWaveTn, StateType
                          <6>3 leaderReachablity[q][w].exists = TRUE
                               BY <5>1,<3>2 DEF UpdateDecidedWaveTn
                          <6>4 w >= decidedWave[q]
                               BY <5>1,<3>2 DEF UpdateDecidedWaveTn
                          <6>5 CASE decidedWave[q] = 0
                               <7>1 leaderSeq[q].current = <<>>
                                    BY <6>5, <2>1 DEF Invariant2
                               <7> QED BY <2>1, <5>1, <6>2, <7>1, EmptyIsPrefix DEF StateType
                          <6>6 CASE decidedWave[q] # 0
                               <7>1 leaderSeq'[q].last = commitWithRef[q][decidedWave[q]]
                                    BY <6>2,<2>1,<4>1, <6>6 DEF Invariant2
                               <7> QED BY <7>1, <4>1,<3>2, <6>1,<6>3,<6>4,<6>6,<2>1 DEF Invariant10
                          <6> QED BY <6>5, <6>6
                     <5>2 CASE p # q
                          <6>1 leaderSeq'[q] = leaderSeq[q]
                               BY <3>2,<4>1,<5>2 DEF UpdateDecidedWaveTn
                          <6> QED BY <2>1, <6>1 DEF ChainMonotonicity, StateType
                     <5> QED BY <5>1,<5>2    
                <4> QED BY <4>1 DEF ChainMonotonicity
           <3> QED BY <3>1,<3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, ChainMonotonicity
           PROVE ChainMonotonicity'
           BY <2>2 DEF vars, ChainMonotonicity
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeCorrectnessLem, Invariant10CorrectnessLem,  Invariant1CorrectnessLem,Invariant2CorrectnessLem, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Wed Jan 31 09:15:04 AEDT 2024 by scholz
\* Last modified Tue Jan 30 19:17:42 AEDT 2024 by Pranav
\* Created Mon Jan 15 13:08:58 AEDT 2024 by Pranav
