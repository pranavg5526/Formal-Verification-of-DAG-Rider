-------------------- MODULE LeaderConsensusVerification --------------------

EXTENDS FiniteSets, 
        Integers, 
        LeaderConsensusSpecification, 
        SequenceOpTheorems,
        Sequences, 
        TLAPS, 
        TLC 

---------------------------------------------------------------------------

Contains(w, S) == \E i \in 1..Len(S): S[i] = w

InductiveInv1 == 
   \A p \in ProcessorSet: 
      decidedWave[p] # 0 => leaderReachablity[p][decidedWave[p]].exists = TRUE

InductiveInv2 == 
   \A p \in ProcessorSet: 
      leaderSeq[p].current = 
         IF decidedWave[p] = 0 
         THEN <<>> 
         ELSE commitWithRef[p][decidedWave[p]]

InductiveInv3 == 
   \A p \in ProcessorSet, w \in WaveSet: 
      \A x \in leaderReachablity[p][w].edges: leaderReachablity[p][x].exists = TRUE

InductiveInv4 == 
   \A p \in ProcessorSet, w, x \in WaveSet: 
      Contains(w, commitWithRef[p][x]) => leaderReachablity[p][w].exists = TRUE

InductiveInv5 == 
   \A p \in ProcessorSet, w, x \in WaveSet: 
      Contains(w, commitWithRef[p][x]) => IsPrefix(commitWithRef[p][w], commitWithRef[p][x])

InductiveInv6 == 
   \A p \in ProcessorSet, w \in WaveSet: 
      leaderReachablity[p][w].exists = TRUE => 
         commitWithRef[p][w] = 
            IF leaderReachablity[p][w].edges = {} 
            THEN <<w>> 
            ELSE Append(commitWithRef[p][max(leaderReachablity[p][w].edges)], w) 

InductiveInv7 == 
   \A p, q \in ProcessorSet, w \in WaveSet: 
      leaderReachablity[p][w].exists = leaderReachablity[q][w].exists => commitWithRef[p][w] = commitWithRef[q][w]

InductiveInv8 == 
   \A p \in ProcessorSet, w \in WaveSet: 
      (\A y \in WaveSet : y > w /\ leaderReachablity[p][y].exists => w \in leaderReachablity[p][y].edges) => 
         (\A y \in WaveSet : y >= w /\ leaderReachablity[p][y].exists => Contains(w, commitWithRef[p][y])) 

InductiveInv9 == 
   \A p, q \in ProcessorSet, w \in WaveSet: 
      decidedWave[p] # 0
      /\ w >= decidedWave[p]
      /\ leaderReachablity[q][w].exists = TRUE => Contains(decidedWave[p], commitWithRef[q][w])

InductiveInv10 == 
   \A p, q \in ProcessorSet, w \in WaveSet: 
      leaderReachablity[p][w].exists = TRUE 
      /\ w >= decidedWave[q] 
      /\ decidedWave[q] # 0 => 
         IsPrefix(commitWithRef[q][decidedWave[q]], commitWithRef[p][w]) 

---------------------------------------------------------------------------

LEMMA MaxInPlt == \A E \in SUBSET(WaveSet) : E # {} =>  max(E) \in E 
      
LEMMA MaxPropertyPlt == \A E \in SUBSET(WaveSet) : \A x \in E: E # {} => x<=max(E)

---------------------------------------------------------------------------

LEMMA SelfIsPrefixLem == \A S \in Seq(WaveSet) : IsPrefix(S, S) = TRUE
      <1>1 \A S \in Seq(WaveSet) : S \o <<>> = S /\ <<>> \in Seq(WaveSet)
           OBVIOUS
      <1> QED BY IsPrefixConcat, <1>1
      
LEMMA TransitiveIsPrefixLem == ASSUME NEW S \in Seq(WaveSet), NEW L \in Seq(WaveSet), NEW M \in Seq(WaveSet), IsPrefix(S, L), IsPrefix(L, M)
                            PROVE IsPrefix(S, M)
      <1>1 \E u, w \in Seq(WaveSet) : L = S \o u /\ M = L \o w
           BY IsPrefixProperties
      <1>2 \A n, m, u \in Seq(WaveSet) : (n \o m) \o u = n \o (m \o u)
           OBVIOUS
      <1>3  \E u, w \in Seq(WaveSet) : M = S \o (u \o w)
           BY <1>1
      <1>4 \A u, w \in Seq(WaveSet) : u \o w \in Seq(WaveSet) 
           OBVIOUS
      <1>5 \A u, w \in Seq(WaveSet) : M = S \o (u \o w) /\ u \o w \in Seq(WaveSet) => IsPrefix(S, M)
           BY IsPrefixConcat
      <1> QED BY <1>5, <1>4, <1>3

LEMMA AppendIsPrefixLem == \A S \in Seq(WaveSet), w \in WaveSet : IsPrefix(S, Append(S, w))
      <1>1 \A S \in Seq(WaveSet), w \in WaveSet : <<w>> \in Seq(WaveSet) /\ Append(S, w) = S \o <<w>>
           OBVIOUS
      <1> QED BY <1>1, IsPrefixConcat
     
---------------------------------------------------------------------------

LEMMA TypeLem == Spec => []StateType
 <1>1 Init => StateType
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
 <1>2 ASSUME StateType, Next
      PROVE StateType'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
           PROVE StateType'
           <3>1 leaderReachablity' \in [ProcessorSet -> [WaveSet -> [exists : BOOLEAN, edges : SUBSET(WaveSet)]]]
                BY  <2>1, <1>2 DEF ProcessorSet, WaveSet, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
           <3>2 commitWithRef' \in [ProcessorSet -> [WaveSet -> Seq(WaveSet)]]
                <4>1 <<w>> \in Seq(WaveSet)
                     BY <2>1 
                <4>2 E # {} =>max(E) \in WaveSet
                     BY MaxInPlt, <2>1
                <4>3 E # {} => Append(commitWithRef[p][max(E)], w) \in Seq(WaveSet)
                     <5>1 E # {} => commitWithRef[p][max(E)] \in Seq(WaveSet)
                          BY <2>1, <4>2, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5> QED BY <5>1, <2>1 
                <4> QED BY  <4>1, <4>3, <2>1, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
           <3> QED BY <3>1, <3>2, <2>1, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
      <2>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
           PROVE StateType'
           <3>1 decidedWave' \in [ProcessorSet -> WaveSet \cup {0}]
                BY  <2>2, <1>2 DEF ProcessorSet, WaveSet, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
           <3>2 leaderSeq' \in [ProcessorSet -> [current : Seq(WaveSet), last : Seq(WaveSet)]]
                <4>1 commitWithRef[p][w] \in Seq(WaveSet) /\ leaderSeq[p].current \in Seq(WaveSet)
                     BY <2>2, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                <4> QED BY <4>1, <2>2, <1>2 DEF ProcessorSet, WaveSet, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
           <3> QED BY <3>1, <3>2, <2>2, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
      <2> QED BY <2>1, <2>2, <1>2 DEF Next
 <1>3 StateType /\ UNCHANGED vars => StateType'
      BY DEF vars, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
 <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec
 

---------------------------------------------------------------------------

LEMMA InductiveInv1Lem == Spec => []InductiveInv1
 <1>1 Init => InductiveInv1
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv1
 <1>2 StateType /\ StateType' /\ InductiveInv1 /\ [Next]_vars => InductiveInv1'
      <2>1 ASSUME StateType, StateType', Next, InductiveInv1
           PROVE InductiveInv1'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE InductiveInv1'
                <4>1 ASSUME NEW q \in ProcessorSet, decidedWave'[q] # 0
                     PROVE leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                     <5>1 decidedWave'[q] \in WaveSet
                          BY <2>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5>2 CASE decidedWave'[q] = w /\ p = q 
                          BY <5>2, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>3 CASE decidedWave'[q] # w \/ p # q
                          <6>1 decidedWave[q] # 0
                               BY <3>1, <2>1, <4>1, <5>3 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 leaderReachablity'[q][decidedWave'[q]].exists = leaderReachablity[q][decidedWave[q]].exists
                               BY <5>3, <3>1, <2>1, <5>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <6>2, <2>1 DEF InductiveInv1
                     <5> QED BY <5>3, <5>2
                <4> QED BY <4>1 DEF InductiveInv1
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE InductiveInv1'
                <4>1 ASSUME NEW q \in ProcessorSet, decidedWave'[q] # 0
                     PROVE leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                     <5>1 decidedWave'[q] \in WaveSet
                          BY <2>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5>2 CASE  p = q 
                          BY <5>2, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                     <5>3 CASE p # q
                          <6>1 decidedWave[q] # 0
                               BY <3>2, <2>1, <4>1, <5>3 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>2 leaderReachablity'[q][decidedWave'[q]].exists = leaderReachablity[q][decidedWave[q]].exists
                               BY <5>3, <3>2, <2>1, <5>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6> QED BY <6>1, <6>2, <2>1 DEF InductiveInv1
                     <5> QED BY <5>3, <5>2
                <4> QED BY <4>1 DEF InductiveInv1
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, InductiveInv1
           PROVE InductiveInv1'
           BY <2>2 DEF vars, InductiveInv1
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec


LEMMA InductiveInv2Lem == Spec => []InductiveInv2
 <1>1 Init => InductiveInv2
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv2
 <1>2 StateType /\ StateType' /\ InductiveInv1 /\ InductiveInv1' /\ InductiveInv2 /\ [Next]_vars => InductiveInv2'
      <2>1 ASSUME StateType, StateType', Next, InductiveInv2, InductiveInv1, InductiveInv1'
           PROVE InductiveInv2'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE InductiveInv2'
                <4>1 ASSUME NEW q \in ProcessorSet 
                     PROVE leaderSeq'[q].current = IF decidedWave'[q] = 0 THEN <<>> ELSE commitWithRef'[q][decidedWave'[q]]
                     <5>1 leaderSeq'[q].current = leaderSeq[q].current
                          BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>2 decidedWave'[q] = decidedWave[q]
                          BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>3 decidedWave'[q] # 0 => commitWithRef'[q][decidedWave'[q]] = commitWithRef[q][decidedWave[q]]
                          <6>1 CASE q = p
                               <7>1 decidedWave[q] # 0 => leaderReachablity[q][decidedWave[q]].exists = TRUE
                                    BY <4>1, <2>1 DEF InductiveInv1
                               <7>2 decidedWave[q] # 0 => w # decidedWave[q]
                                    BY <7>1, <3>1, <6>1  DEF UpdateWaveTn
                               <7> QED BY <7>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 CASE q # p
                               BY <6>2, <5>2, <3>1, <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <6>2
                     <5> QED BY <5>1, <5>2, <5>3, <2>1 DEF InductiveInv2
                <4> QED BY <4>1 DEF InductiveInv2  
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE InductiveInv2'
                <4>1 ASSUME NEW q \in ProcessorSet 
                     PROVE leaderSeq'[q].current = IF decidedWave'[q] = 0 THEN <<>> ELSE commitWithRef'[q][decidedWave'[q]]
                     <5>1 CASE p = q
                          <6>1 decidedWave'[q] = w
                               BY <5>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>2 leaderSeq'[q].current = commitWithRef'[q][decidedWave'[q]]
                               BY <5>1, <3>2, <2>1, <6>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6> QED BY <6>1, <6>2, <3>1 DEF WaveSet
                     <5>2 CASE p # q
                          <6>1 leaderSeq'[q].current =leaderSeq[q].current
                               BY <4>1, <5>2, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>2 decidedWave'[q] = decidedWave[q]
                               BY <4>1, <5>2, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>3 decidedWave'[q] # 0 => commitWithRef'[q][decidedWave'[q]] = commitWithRef[q][decidedWave[q]]
                               BY <5>2, <6>2, <3>2, <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6> QED BY <6>1, <6>2, <6>3, <2>1 DEF InductiveInv2
                     <5> QED BY <5>1, <5>2
                <4> QED BY <4>1 DEF InductiveInv2  
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, InductiveInv2
           PROVE InductiveInv2'
           BY <2>2 DEF vars, InductiveInv2
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, InductiveInv1Lem, PTL DEF Spec
 
  
LEMMA InductiveInv3Lem == Spec => []InductiveInv3
 <1>1 Init => InductiveInv3
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv3
 <1>2 StateType /\ StateType' /\ InductiveInv3 /\ [Next]_vars => InductiveInv3'
      <2>1 ASSUME StateType, StateType', Next, InductiveInv3
           PROVE InductiveInv3'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE InductiveInv3'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in leaderReachablity'[q][x].edges
                     PROVE leaderReachablity'[q][y].exists = TRUE
                     <5>1 y \in WaveSet
                          BY <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5>2 CASE q = p /\ x = w
                          BY <5>2, <3>1, <2>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>3 CASE q # p \/ x # w
                          <6>1 leaderReachablity'[q][x].edges = leaderReachablity[q][x].edges
                               BY <5>3, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 leaderReachablity[q][y].exists = leaderReachablity'[q][y].exists
                               <7>1 w # y \/ q # p
                                    <8>1 leaderReachablity[q][y].exists = TRUE
                                         BY <6>1, <4>1, <2>1 DEF InductiveInv3
                                    <8> QED BY <8>1, <3>1, <4>1 DEF UpdateWaveTn
                               <7> QED BY <7>1, <5>1, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <6>2, <4>1, <2>1 DEF InductiveInv3, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5> QED  BY <5>2, <5>3 
                <4> QED BY <4>1 DEF InductiveInv3
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE InductiveInv3'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in leaderReachablity'[q][x].edges
                     PROVE leaderReachablity'[q][y].exists = TRUE 
                     <5>1 leaderReachablity'[q][x].edges = leaderReachablity[q][x].edges 
                          BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                     <5>2 leaderReachablity'[q][y].exists = leaderReachablity[q][y].exists
                          BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                     <5> QED BY <5>1, <5>2, <4>1, <2>1 DEF InductiveInv3
                <4> QED BY <4>1 DEF InductiveInv3
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, InductiveInv3
           PROVE InductiveInv3'
           BY <2>2 DEF vars, InductiveInv3
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec      


LEMMA InductiveInv4Lem == Spec => []InductiveInv4
 <1>1 Init => InductiveInv4
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv4, Contains
 <1>2 StateType /\ StateType' /\ InductiveInv4 /\ [Next]_vars => InductiveInv4'
      <2>1 ASSUME StateType, StateType', Next, InductiveInv4
           PROVE InductiveInv4'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE InductiveInv4'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y])
                     PROVE leaderReachablity'[q][x].exists = TRUE
                     <5>1 CASE p = q
                          <6>1 CASE x = w
                               BY <6>1, <5>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 CASE x # w
                               <7>1 CASE y # w
                                    BY <7>1, <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv4, UpdateWaveTn
                               <7>2 CASE y = w
                                    <8>1 E # {}
                                         BY <6>2, <4>1, <3>1, <7>2, <5>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn, Contains
                                    <8>2 Contains(x, commitWithRef[q][max(E)])
                                         BY <6>2, <4>1, <3>1, <7>2, <5>1, <2>1, <8>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn, Contains
                                    <8>3 leaderReachablity'[q][x].exists = leaderReachablity[q][x].exists
                                         BY <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8> QED BY <8>2, <8>1, <8>3, MaxInPlt, <4>1, <2>1, <3>1 DEF InductiveInv4
                               <7> QED BY <7>1, <7>2
                          <6> QED BY <6>1, <6>2
                     <5>2 CASE p # q
                          BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv4, UpdateWaveTn
                     <5> QED BY <5>1, <5>2 
                <4> QED BY <4>1 DEF InductiveInv4
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE InductiveInv4'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y])
                     PROVE leaderReachablity'[q][x].exists = TRUE
                     BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv4, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF InductiveInv4
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, InductiveInv4
           PROVE InductiveInv4'
           BY <2>2 DEF vars, InductiveInv4
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec
 
 
LEMMA InductiveInv5Lem == Spec => []InductiveInv5
 <1>1 Init => InductiveInv5
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv5, Contains
 <1>2 StateType /\ StateType' /\ InductiveInv5 /\ [Next]_vars /\ InductiveInv4 /\ InductiveInv4' => InductiveInv5'
      <2>1 ASSUME StateType, StateType', Next, InductiveInv5, InductiveInv4, InductiveInv4'
           PROVE InductiveInv5'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE InductiveInv5'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y])
                     PROVE IsPrefix(commitWithRef'[q][x], commitWithRef'[q][y])
                     <5>1 CASE p = q
                          <6>1 CASE x = w
                               <7>1 CASE y = w
                                    BY <7>1, <6>1, <4>1, <2>1, SelfIsPrefixLem DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                               <7>2 CASE y # w
                                    <8>1 leaderReachablity[q][x].exists = TRUE
                                         <9>1 Contains(x, commitWithRef[q][y])
                                              <10>1 commitWithRef'[q][y] = commitWithRef[q][y]
                                                    BY <7>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                              <10> QED BY <4>1, <10>1
                                         <9> QED BY <9>1, <4>1, <2>1 DEF InductiveInv4
                                    <8>2 leaderReachablity[q][x].exists = FALSE
                                         BY <6>1, <5>1, <3>1 DEF UpdateWaveTn
                                    <8> QED BY <8>1, <8>2
                               <7> QED BY <7>1, <7>2
                          <6>2 CASE x # w
                               <7>1 CASE y # w
                                    BY <7>1, <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv5, UpdateWaveTn
                               <7>2 CASE y = w
                                    <8>1 E # {} /\ Contains(x, commitWithRef[q][max(E)])
                                         BY <5>1, <7>2, <6>2, <4>1, <3>1, <2>1 DEF Contains, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>2 max(E) \in WaveSet
                                         BY <8>1, <3>1, MaxInPlt
                                    <8>3 commitWithRef'[q][x] = commitWithRef[q][x]
                                         BY <6>2, <3>1, <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>4 IsPrefix(commitWithRef'[q][x], commitWithRef[q][max(E)])
                                         BY <8>1, <8>2, <8>3, <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv5
                                    <8>5 IsPrefix(commitWithRef[q][max(E)], commitWithRef'[q][y])
                                         BY <8>1, <5>1, <7>2, <2>1, <3>1, AppendIsPrefixLem DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8> QED BY <8>2, <8>4, <8>5, TransitiveIsPrefixLem, <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                               <7> QED BY <7>1, <7>2
                          <6> QED BY <6>1, <6>2
                     <5>2 CASE p # q
                          BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv5, UpdateWaveTn
                     <5> QED BY <5>1, <5>2 
                <4> QED BY <4>1 DEF InductiveInv5
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE InductiveInv5'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y])
                     PROVE IsPrefix(commitWithRef'[q][x], commitWithRef'[q][y])
                     BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv5, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF InductiveInv5
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, InductiveInv5
           PROVE InductiveInv5'
           BY <2>2 DEF vars, InductiveInv5
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, InductiveInv4Lem, PTL DEF Spec


LEMMA InductiveInv6Lem == Spec => []InductiveInv6
 <1>1 Init => InductiveInv6
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv6
 <1>2 StateType /\ StateType' /\ InductiveInv6 /\ [Next]_vars /\ InductiveInv3 /\ InductiveInv3' => InductiveInv6'
      <2>1 ASSUME StateType, StateType', Next, InductiveInv6, InductiveInv3, InductiveInv3'
           PROVE InductiveInv6'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE InductiveInv6'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = TRUE
                     PROVE commitWithRef'[q][x] = IF leaderReachablity'[q][x].edges = {} THEN <<x>> ELSE Append(commitWithRef'[q][max(leaderReachablity'[q][x].edges)], x)
                     <5>1 CASE q = p /\ x = w
                          <6>1 leaderReachablity'[q][x].edges = E
                               BY <5>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                          <6>3 E # {} => commitWithRef'[q][max(E)] = commitWithRef[q][max(E)]
                               <7>1 E # {} => w # max(E)
                                    BY MaxInPlt, <3>1 DEF UpdateWaveTn
                               <7> QED BY <7>1, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <5>1, <4>1, <3>1, <2>1, <6>3 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>2 CASE q # p \/ x # w
                          <6>1 commitWithRef'[q][x] = commitWithRef[q][x] 
                               BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 leaderReachablity'[q][x].edges = leaderReachablity[q][x].edges /\ leaderReachablity'[q][x].exists = leaderReachablity[q][x].exists
                               BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>3 leaderReachablity'[q][x].edges # {} => commitWithRef'[q][max(leaderReachablity'[q][x].edges)] = commitWithRef[q][max(leaderReachablity[q][x].edges)]
                               <7>1 leaderReachablity[q][x].edges # {} => max(leaderReachablity[q][x].edges) # w \/ q # p
                                    <8>1 leaderReachablity[q][x].edges # {} => leaderReachablity[q][max(leaderReachablity[q][x].edges)].exists = TRUE
                                         <9>1 leaderReachablity[q][x].edges \in SUBSET(WaveSet)
                                              BY <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                         <9>2 leaderReachablity[q][x].edges # {} => max(leaderReachablity[q][x].edges) \in leaderReachablity[q][x].edges
                                              BY <4>1, <2>1, <9>1, MaxInPlt DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                         <9> QED BY <2>1, <4>1, <3>1, <9>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv3
                                    <8> QED BY <8>1, <3>1, <4>1, <2>1, MaxInPlt DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7> QED BY <7>1, <4>1, <3>1, <2>1, <6>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <6>2, <6>3, <4>1, <2>1 DEF InductiveInv6
                     <5> QED BY <5>1, <5>2
                <4> QED BY <4>1 DEF InductiveInv6
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE InductiveInv6'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = TRUE
                     PROVE commitWithRef'[q][x] = IF leaderReachablity'[q][x].edges = {} THEN <<x>> ELSE Append(commitWithRef'[q][max(leaderReachablity'[q][x].edges)], x)
                     BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv6, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF InductiveInv6
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, InductiveInv6
           PROVE InductiveInv6'
           BY <2>2 DEF vars, InductiveInv6
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, InductiveInv3Lem, PTL DEF Spec
 

LEMMA InductiveInv7Lem == Spec => []InductiveInv7
 <1>1 Init => InductiveInv7
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv7
 <1>2 StateType /\ StateType' /\ InductiveInv7 /\ [Next]_vars /\ InductiveInv6 /\ InductiveInv3 => InductiveInv7'
      <2>1 ASSUME StateType, StateType', Next, InductiveInv7, InductiveInv6, InductiveInv3
           PROVE InductiveInv7'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE InductiveInv7'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = leaderReachablity'[r][x].exists
                     PROVE commitWithRef'[q][x] = commitWithRef'[r][x]
                     <5>1 CASE q = r
                          BY <5>1
                     <5>2 CASE q # r
                          <6>1 CASE x # w
                               BY <6>1, <4>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv7
                          <6>2 CASE x = w
                               <7>1 CASE q = p
                                    <8>1 leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists /\ commitWithRef[r][x] = commitWithRef'[r][x]
                                         BY <7>1, <5>2, <4>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                    <8>2 leaderReachablity'[q][x].exists /\ leaderReachablity'[r][x].exists
                                         BY <7>1, <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>3 commitWithRef[r][x] = IF leaderReachablity[r][x].edges = {} THEN <<x>> ELSE Append(commitWithRef[r][max(leaderReachablity[r][x].edges)], x)
                                         BY <8>1, <4>1, <2>1, <8>2 DEF InductiveInv6
                                    <8>4 E  = leaderReachablity[r][x].edges
                                         BY <6>2, <4>1, <3>1, <8>1, <8>2 DEF UpdateWaveTn
                                    <8>5 commitWithRef'[q][x] = IF E = {} THEN <<x>> ELSE Append(commitWithRef[q][max(E)], x)
                                         BY <7>1, <6>2, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>7 E # {} => leaderReachablity[r][max(E)].exists /\ leaderReachablity[q][max(E)].exists
                                         BY <8>4, MaxInPlt, <3>1, <4>1, <2>1, <7>1 DEF InductiveInv3, UpdateWaveTn
                                    <8>6 E # {} => commitWithRef[q][max(E)] = commitWithRef[r][max(E)]
                                         BY <4>1, <3>1, MaxInPlt, <2>1, <8>7 DEF InductiveInv7
                                    <8> QED BY <8>3, <8>4, <8>5, <8>6, <8>1
                               <7>2 CASE r = p
                                    <8>1 leaderReachablity'[q][x].exists = leaderReachablity[q][x].exists /\ commitWithRef[q][x] = commitWithRef'[q][x]
                                         BY <7>2, <5>2, <4>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                    <8>2 leaderReachablity'[r][x].exists /\ leaderReachablity'[q][x].exists
                                         BY <7>2, <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>3 commitWithRef[q][x] = IF leaderReachablity[q][x].edges = {} THEN <<x>> ELSE Append(commitWithRef[q][max(leaderReachablity[q][x].edges)], x)
                                         BY <8>1, <4>1, <2>1, <8>2 DEF InductiveInv6
                                    <8>4 E  = leaderReachablity[q][x].edges
                                         BY <6>2, <4>1, <3>1, <8>1, <8>2 DEF UpdateWaveTn
                                    <8>5 commitWithRef'[r][x] = IF E = {} THEN <<x>> ELSE Append(commitWithRef[r][max(E)], x)
                                         BY <7>2, <6>2, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>7 E # {} => leaderReachablity[q][max(E)].exists /\ leaderReachablity[r][max(E)].exists
                                         BY <8>4, MaxInPlt, <3>1, <4>1, <2>1, <7>2 DEF InductiveInv3, UpdateWaveTn
                                    <8>6 E # {} => commitWithRef[r][max(E)] = commitWithRef[q][max(E)]
                                         BY <4>1, <3>1, MaxInPlt, <2>1, <8>7 DEF InductiveInv7
                                    <8> QED BY <8>3, <8>4, <8>5, <8>6, <8>1     
                               <7>3 CASE q # p /\ r # p
                                    BY <7>3, <4>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv7
                               <7> QED BY <7>1, <7>2, <7>3
                          <6> QED BY <6>1, <6>2
                     <5> QED BY <5>1, <5>2
                <4> QED BY <4>1 DEF InductiveInv7
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE InductiveInv7'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = leaderReachablity'[r][x].exists
                     PROVE commitWithRef'[q][x] = commitWithRef'[r][x]
                     BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv7, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF InductiveInv7
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, InductiveInv7
           PROVE InductiveInv7'
           BY <2>2 DEF vars, InductiveInv7
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, InductiveInv3Lem, InductiveInv6Lem, PTL DEF Spec


LEMMA InductiveInv8Lem == Spec => []InductiveInv8
 <1>1 Init => InductiveInv8
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv8
 <1>2 StateType /\ StateType' /\ InductiveInv8 /\ [Next]_vars /\ InductiveInv6' => InductiveInv8'
      <2>1 ASSUME StateType, StateType', Next, InductiveInv8, InductiveInv6'
           PROVE InductiveInv8'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE InductiveInv8'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW z \in WaveSet, z >= x, leaderReachablity'[q][z].exists, \A y \in WaveSet : y > x /\ leaderReachablity'[q][y].exists => x \in leaderReachablity'[q][y].edges
                     PROVE Contains(x, commitWithRef'[q][z]) 
                     <5>1 CASE x = z
                          <6>1 commitWithRef'[q][z] = IF leaderReachablity'[q][z].edges # {} THEN Append(commitWithRef'[q][max(leaderReachablity'[q][z].edges)], z) ELSE <<z>>
                               BY  <2>1, <4>1 DEF InductiveInv6
                          <6>2 leaderReachablity'[q][z].edges # {} => Contains(z, commitWithRef'[q][z]) 
                               BY <6>1 DEF Contains
                          <6> QED BY <5>1, <6>1, <6>2 DEF Contains
                     <5>2 CASE x # z
                          <6>1 z > x
                               BY <5>2, <4>1
                          <6>2 \A y \in WaveSet : y > x /\ leaderReachablity[q][y].exists => x \in leaderReachablity[q][y].edges
                               <7>1 \A y \in WaveSet : y > x /\ (y # w \/ q # p) /\ leaderReachablity[q][y].exists => x \in leaderReachablity[q][y].edges
                                    BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7>2 \A y \in WaveSet : y > x /\ (y = w /\ q = p) => leaderReachablity[q][y].exists = FALSE
                                    BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7> QED BY <7>1, <7>2
                          <6>3 CASE p = q /\ w = z
                               <7>1 leaderReachablity'[q][z].edges = E
                                    BY <2>1, <6>3, <3>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                               <7>2 x \in E
                                    BY <6>1, <4>1, <7>1
                               <7>3 commitWithRef'[q][z] = Append(commitWithRef'[q][max(E)], z)
                                    BY  <2>1, <4>1, <7>1, <7>2 DEF InductiveInv6
                               <7>4 max(E) # w /\ max(E) >= x
                                    BY <7>2, MaxInPlt, <3>1, MaxPropertyPlt DEF UpdateWaveTn
                               <7>5 leaderReachablity[q][max(E)].exists
                                    BY <6>3, <3>1, <7>2, MaxInPlt DEF UpdateWaveTn
                               <7>6 commitWithRef'[q][max(E)] = commitWithRef[q][max(E)]
                                    BY <7>4, <3>1, <6>3, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7>7 Contains(x, commitWithRef[q][max(E)])
                                    BY <7>6, <7>5, <6>2, <7>4, <7>2, <3>1, <2>1, <4>1, MaxInPlt DEF InductiveInv8
                               <7> QED BY <7>7, <7>6, <7>3 DEF Contains
                          <6>4 CASE p # q \/ w # z
                               BY <6>2, <4>1, <6>4, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn, InductiveInv8
                          <6> QED BY <6>3, <6>4
                     <5> QED BY <5>1, <5>2
                <4> QED BY <4>1 DEF InductiveInv8
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE InductiveInv8'
                BY <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, InductiveInv8, UpdateDecidedWaveTn
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, InductiveInv8
           PROVE InductiveInv8'
           BY <2>2 DEF vars, InductiveInv8
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, InductiveInv6Lem, PTL DEF Spec


LEMMA InductiveInv9Lem == Spec => []InductiveInv9
 <1>1 Init => InductiveInv9
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv9
 <1>2 StateType /\ StateType' /\ InductiveInv9 /\ [Next]_vars /\ InductiveInv8 /\ InductiveInv6 /\ InductiveInv3 => InductiveInv9'
      <2>1 ASSUME StateType, StateType', Next, InductiveInv8, InductiveInv6, InductiveInv3, InductiveInv9
           PROVE InductiveInv9'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE InductiveInv9'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, decidedWave'[q] # 0, x >= decidedWave'[q], leaderReachablity'[r][x].exists = TRUE
                     PROVE Contains(decidedWave'[q], commitWithRef'[r][x])
                     <5>1 decidedWave'[q] = decidedWave[q]
                          BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>2 CASE x # w
                          <6>1 commitWithRef'[r][x] = commitWithRef[r][x] /\ leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists
                               BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <5>1, <4>1, <2>1 DEF InductiveInv9
                     <5>3 CASE x = w
                          <6>1 CASE r = p
                               <7>1 E # {} => commitWithRef'[r][x] = Append(commitWithRef[r][max(E)], x)
                                    BY <3>1, <2>1, <6>1, <5>3 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                               <7>2 CASE decidedWave'[q] = x 
                                    <8>1 Contains(x, commitWithRef'[r][x])
                                         BY <7>1, <3>1, <2>1, <5>3, <6>1 DEF Contains, UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                    <8> QED BY <8>1, <7>2
                               <7>3 CASE decidedWave'[q] # x 
                                    <8>1 decidedWave'[q] \in E /\ E # {}
                                         <9>1 decidedWave'[q] < x
                                              BY <7>3, <4>1
                                         <9> QED BY <9>1, <5>3, <4>1, <3>1 DEF UpdateWaveTn
                                    <8>2 Contains(decidedWave'[q], commitWithRef[r][max(E)])
                                         <9>1 max(E) \in E
                                              BY <8>1, <3>1, MaxInPlt
                                         <9>2 decidedWave'[q] =< max(E)
                                              BY <8>1, MaxPropertyPlt, <3>1 DEF max
                                         <9>3 leaderReachablity[r][max(E)].exists = TRUE
                                              BY <8>1, <6>1, <3>1, <9>1 DEF UpdateWaveTn
                                         <9> QED BY <9>1, <4>1, <9>2, <9>3, <2>1, <5>1 DEF InductiveInv9, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                    <8> QED BY <8>1, <7>1, <8>2 DEF Contains
                               <7> QED BY <7>2, <7>3
                          <6>2 CASE r # p
                               <7>1 commitWithRef'[r][x] = commitWithRef[r][x] /\ leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists
                                    BY <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7> QED BY <7>1, <5>1, <4>1, <2>1 DEF InductiveInv9
                          <6> QED BY <6>1, <6>2
                     <5> QED BY <5>2, <5>3
                <4> QED BY <4>1 DEF InductiveInv9
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE InductiveInv9'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, decidedWave'[q] # 0, x >= decidedWave'[q], leaderReachablity'[r][x].exists = TRUE
                     PROVE Contains(decidedWave'[q], commitWithRef'[r][x])
                     <5>1 commitWithRef'[r][x] = commitWithRef[r][x] /\ leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists
                          BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                     <5>2 CASE q # p
                          <6>1 decidedWave'[q] = decidedWave[q]
                               BY <5>2, <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6> QED BY <6>1, <5>1, <2>1, <4>1 DEF InductiveInv9
                     <5>3 CASE q = p
                          <6>1 decidedWave'[q] = w
                               BY <5>3, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>2 commitWithRef[r][x] = IF leaderReachablity[r][x].edges # {} THEN Append(commitWithRef[r][max(leaderReachablity[r][x].edges)], x) ELSE <<x>>
                               BY <4>1, <2>1, <5>1 DEF InductiveInv6
                          <6>3 CASE q = r
                               <7>1 CASE x = w
                                    <8>1 Contains(x, commitWithRef[r][x])
                                         <9>1 CASE leaderReachablity[r][x].edges # {}
                                             BY <9>1, <6>2 DEF Contains
                                         <9>2 CASE leaderReachablity[r][x].edges = {} 
                                             BY <9>2, <6>2 DEF Contains
                                         <9> QED BY <9>1, <9>2
                                    <8> QED BY <8>1, <7>1, <6>1, <5>1
                               <7>2 CASE x # w
                                    <8>1 x > w
                                         BY <7>2, <6>1, <4>1
                                    <8>2 leaderReachablity[r][x].exists = FALSE
                                         BY <8>1, <6>3, <5>3, <3>2, <2>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                                    <8> QED BY <8>2, <5>1, <4>1
                              <7> QED BY <7>1, <7>2
                          <6>4 CASE q # r
                              <7>1 CASE x = w
                                   <8>1 Contains(x, commitWithRef[r][x])
                                         <9>1 CASE leaderReachablity[r][x].edges # {}
                                             BY <9>1, <6>2 DEF Contains
                                         <9>2 CASE leaderReachablity[r][x].edges = {} 
                                             BY <9>2, <6>2 DEF Contains
                                         <9> QED BY <9>1, <9>2
                                   <8> QED BY <8>1, <7>1, <6>1, <5>1
                              <7>2 CASE x # w
                                   <8>1 w \in leaderReachablity[r][x].edges /\ leaderReachablity[r][x].edges # {}
                                        <9>1 w < x
                                             BY <7>2, <4>1, <6>1
                                        <9> QED BY <9>1, <5>3, <4>1, <3>2, <6>2, <4>1 DEF UpdateDecidedWaveTn
                                   <8>2 leaderReachablity[r][x].edges \in SUBSET(WaveSet)
                                        BY <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                   <8>3 Contains(w, commitWithRef[r][max(leaderReachablity[r][x].edges)])     
                                        <9>1 max(leaderReachablity[r][x].edges) \in leaderReachablity[r][x].edges
                                             BY <8>1, <4>1, MaxInPlt, <8>2
                                        <9>2 w =< max(leaderReachablity[r][x].edges)
                                             BY <8>1, MaxPropertyPlt, <3>1, <8>2 DEF max
                                        <9>3 leaderReachablity[r][max(leaderReachablity[r][x].edges)].exists = TRUE
                                             BY <4>1, <2>1, <9>1 DEF InductiveInv3
                                        <9>4 \A z \in WaveSet : z >= w /\ leaderReachablity[r][z].exists = TRUE => Contains(w, commitWithRef[r][z])
                                             BY <4>1, <3>2, <2>1 DEF InductiveInv8, UpdateDecidedWaveTn
                                        <9> QED BY <9>1, <9>2, <9>3, <9>4, <8>2
                                   <8>4 Contains(w, commitWithRef[r][max(leaderReachablity[r][x].edges)])  => Contains(w, Append(commitWithRef[r][max(leaderReachablity[r][x].edges)], x))
                                        BY DEF Contains
                                   <8> QED BY <8>1, <8>4, <6>2, <8>3, <6>1, <5>1 DEF Contains 
                              <7> QED BY <7>1, <7>2
                          <6> QED BY <6>3, <6>4
                     <5> QED BY <5>2, <5>3
                <4> QED BY <4>1 DEF InductiveInv9
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, InductiveInv9
           PROVE InductiveInv9'
           BY <2>2 DEF vars, InductiveInv9
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, InductiveInv8Lem, InductiveInv6Lem, InductiveInv3Lem, PTL DEF Spec


LEMMA InductiveInv10Lem == Spec => []InductiveInv10
 <1>1 Init => InductiveInv10
    BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, InductiveInv10
 <1>2 InductiveInv1 /\ InductiveInv1' /\ InductiveInv4 /\ InductiveInv4' /\ InductiveInv7 /\ InductiveInv7' /\ InductiveInv5 /\ InductiveInv5'/\ InductiveInv9 /\ InductiveInv9' /\ StateType /\ StateType' /\ InductiveInv10 /\ [Next]_vars => InductiveInv10'
      <2>1 ASSUME InductiveInv9, InductiveInv9', StateType, StateType', InductiveInv10, [Next]_vars, InductiveInv1, InductiveInv1', InductiveInv4, InductiveInv4', InductiveInv7, InductiveInv7', InductiveInv5, InductiveInv5'
           PROVE InductiveInv10'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW w \in WaveSet, leaderReachablity'[p][w].exists = TRUE, w >= decidedWave'[q], decidedWave'[q] # 0
                PROVE IsPrefix(commitWithRef'[q][decidedWave'[q]], commitWithRef'[p][w])
                <4>1 Contains(decidedWave'[q], commitWithRef'[p][w]) 
                     BY <3>1, <2>1 DEF InductiveInv9
                <4>2 decidedWave'[q] \in WaveSet
                     BY <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                <4>3 commitWithRef'[p][decidedWave'[q]] = commitWithRef'[q][decidedWave'[q]]
                     <5>1 leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                          BY <3>1, <2>1 DEF InductiveInv1    
                     <5>2 leaderReachablity'[p][decidedWave'[q]].exists = TRUE
                          BY <3>1, <4>1, <4>2, <2>1 DEF InductiveInv4
                     <5> QED BY <5>1, <5>2, <4>2, <3>1, <2>1 DEF InductiveInv7
                <4>4 IsPrefix(commitWithRef'[p][decidedWave'[q]], commitWithRef'[p][w])
                     BY <4>1, <4>2, <3>1, <2>1 DEF InductiveInv5
                <4> QED BY <4>3, <4>4
           <3> QED BY <3>1 DEF InductiveInv10
      <2> QED BY <2>1     
 <1> QED BY <1>1, <1>2, PTL, TypeLem, InductiveInv1Lem, InductiveInv4Lem, InductiveInv7Lem, InductiveInv5Lem, InductiveInv9Lem DEF Spec             


---------------------------------------------------------------------------

THEOREM ConsistencyThm == Spec => []Consistency
  <1>1 Init => Consistency
      BY SelfIsPrefixLem DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, Consistency
 <1>2 StateType /\ StateType' /\ InductiveInv10 /\ InductiveInv10' /\ InductiveInv1 /\ InductiveInv1'/\ InductiveInv2 /\ InductiveInv2' /\ [Next]_vars /\ Consistency => Consistency'
      <2>1 ASSUME StateType, StateType', InductiveInv10, InductiveInv10', [Next]_vars, Consistency, InductiveInv1, InductiveInv1', InductiveInv2, InductiveInv2'
           PROVE Consistency'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, decidedWave'[p] <= decidedWave'[q]
                PROVE IsPrefix(leaderSeq'[p].current, leaderSeq'[q].current)
                <4>1 CASE decidedWave'[p] = 0 /\ decidedWave'[q] = 0
                     <5>1 leaderSeq'[p].current = <<>> /\ leaderSeq'[q].current = <<>>
                          BY <4>1, <2>1, <3>1 DEF InductiveInv2
                     <5> QED BY <5>1, SelfIsPrefixLem
                <4>2 CASE decidedWave'[p] = 0 /\ decidedWave'[q] # 0
                     <5>1 leaderSeq'[p].current = <<>>
                          BY <4>2, <2>1, <3>1 DEF InductiveInv2
                     <5> QED BY <5>1, <2>1, EmptyIsPrefix DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                <4>3 CASE decidedWave'[p] # 0 /\ decidedWave'[q] # 0
                     <5>1 leaderSeq'[p].current = commitWithRef'[p][decidedWave'[p]] /\ leaderSeq'[q].current = commitWithRef'[q][decidedWave'[q]]
                          BY <4>3, <2>1, <3>1 DEF InductiveInv2
                     <5>2 decidedWave'[q] \in WaveSet
                          BY <2>1, <4>3 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5>3 leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                          BY <2>1, <3>1, <4>3 DEF InductiveInv1
                     <5> QED BY <5>1, <5>2, <5>3, <2>1, <3>1, <4>3 DEF InductiveInv10
                <4> QED BY <3>1, <4>1, <4>2, <4>3, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, WaveSet
           <3> QED BY <3>1 DEF Consistency
      <2> QED BY <2>1
 <1> QED BY  <1>1, <1>2, TypeLem, InductiveInv10Lem, InductiveInv1Lem, InductiveInv2Lem, PTL DEF Spec


THEOREM  MonotonicityThm == Spec => []Monotonicity
 <1>1 Init => Monotonicity
      BY SelfIsPrefixLem DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, Monotonicity
 <1>2 StateType /\ StateType' /\ InductiveInv10 /\ InductiveInv10' /\ InductiveInv1 /\ InductiveInv1'/\ InductiveInv2 /\ InductiveInv2' /\ [Next]_vars /\ Monotonicity => Monotonicity'
      <2>1 ASSUME StateType, StateType', InductiveInv10, InductiveInv10', Next, Monotonicity,  InductiveInv1, InductiveInv1', InductiveInv2, InductiveInv2'
           PROVE Monotonicity'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Monotonicity'
                BY <3>1, <2>1 DEF Monotonicity, UpdateWaveTn
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Monotonicity'
                <4>1 ASSUME NEW q \in ProcessorSet
                     PROVE IsPrefix(leaderSeq'[q].last, leaderSeq'[q].current)
                     <5>1 CASE p = q
                          <6>1 leaderSeq'[q].current = commitWithRef[q][w]
                               BY <5>1, <3>2, <2>1 DEF UpdateDecidedWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                          <6>2 leaderSeq'[q].last = leaderSeq[q].current
                               BY <5>1, <3>2, <2>1 DEF UpdateDecidedWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                          <6>3 leaderReachablity[q][w].exists = TRUE
                               BY <5>1, <3>2 DEF UpdateDecidedWaveTn
                          <6>4 w >= decidedWave[q]
                               BY <5>1, <3>2 DEF UpdateDecidedWaveTn
                          <6>5 CASE decidedWave[q] = 0
                               <7>1 leaderSeq[q].current = <<>>
                                    BY <6>5, <2>1 DEF InductiveInv2
                               <7> QED BY <2>1, <5>1, <6>2, <7>1, EmptyIsPrefix DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                          <6>6 CASE decidedWave[q] # 0
                               <7>1 leaderSeq'[q].last = commitWithRef[q][decidedWave[q]]
                                    BY <6>2, <2>1, <4>1, <6>6 DEF InductiveInv2
                               <7> QED BY <7>1, <4>1, <3>2, <6>1, <6>3, <6>4, <6>6, <2>1 DEF InductiveInv10
                          <6> QED BY <6>5, <6>6
                     <5>2 CASE p # q
                          <6>1 leaderSeq'[q] = leaderSeq[q]
                               BY <3>2, <4>1, <5>2 DEF UpdateDecidedWaveTn
                          <6> QED BY <2>1, <6>1 DEF Monotonicity, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5> QED BY <5>1, <5>2    
                <4> QED BY <4>1 DEF Monotonicity
           <3> QED BY <3>1, <3>2, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Monotonicity
           PROVE Monotonicity'
           BY <2>2 DEF vars, Monotonicity
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, InductiveInv10Lem, InductiveInv1Lem, InductiveInv2Lem, PTL DEF Spec


=============================================================================
