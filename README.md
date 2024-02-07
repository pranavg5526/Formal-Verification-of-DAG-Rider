# Formal Verification of DAG-Rider

In this work, we formalize the DAG-based consensus protocol called DAG-Rider in TLA+ and prove the safety properties with the TLA+ proof system. The DAG-Rider article can be found here: 
https://arxiv.org/abs/2102.08325

The formalization requires a refinement approach for modelling the consensus. In an abstracted model (LeaderConsensus), we first show the safety of DAG-based consensus on leaders and then further refine the specification to encompass all messages for all processes (DAGRider). The specification consists of 683 (with comments) lines, and the proof system verifies 1922 obligations in approximately 5 minutes.

A common approach to formally model procedural code in TLA+ is to specify a discrete transition system whose traces correspond to possible executions of the code. The naive translation from the pseudo-code (by setting every variable from the protocol, including a variable for each process's current line number, to be a variable in the specification) into a TLA+ specification is not viable. This model, while direct, is very fine-grained, rendering the proofs of properties of interest extremely tedious.

We employ several abstraction techniques to obtain a more concise and tractable model: they remove unnecessary details and produce a specification amenable to proofs. First, we employ a procedural abstraction that ignores all states internal to a procedure and only represents each procedure's input/output behaviour in the DAG-Rider protocol. For instance, in the wave-ready procedure of [1], the relevant variables are decidedWave, deliveredVertices, and leadersStack, but not the loop variable w'. Second, because we focus on safety properties, we remove features only required for liveness and have no impact on the safety proof. For instance, random coin tosses can be replaced with deterministic ones. Third, we use memoization to efficiently compute the values taken by recursive functions by introducing a fresh state variable that stores the needed information to evaluate recursive functions in a single step. Finally, we separate the concerns and break the safety property into two, namely (1) consistent communication and (2) consistent leader election. For (1), we model the DAG construction and show that the causal histories agree for the same vertex in the DAG of two different processes and that there is no equivocation of blocks by faulty processes. For (2), we model the consensus protocol and prove that the same leaders are elected in the same order. 

To obtain a complete yet simple model of the consensus protocol, we observe that it only needs reachability information associated with wave leader vertices to commit leaders and, therefore, abstract the content of DAG into the so-called leaderReachablity record. We combine consensus protocol specifications in DAG construction specifications to obtain one of the DAG-Rider protocols.

Given our faithful specification of DAG-Rider in TLA+, we prove its expected safety properties (DAGConsistency, LeaderConsistency, LeaderMonotonicity) by identifying invariants and proving them within TLA-PS. When using TLA-PS and similar proof systems, the most challenging task is to develop relevant inductive invariants (that hold initially and are preserved when taking transitions). 

For DAG-Rider, to prove the consistency of communication during the DAG construction, we identified six new invariants, and to prove the consistency of leader election, we identified ten new invariants. We prove some of these invariants independently while others with the assumption of some of the already proven invariants; this dependency is described in the following figure:

![image](https://github.com/pranavg5526/Formal-Verification-of-DAG-Rider/assets/140618144/e2f0ee5a-629d-4cd9-b9d5-90cabfaaf13a)

Reading suggestion: 

The specification and verification files should be read in the following order, someone who is just interested in specification can skip reading verification files:

LeaderConsensusSpecification -> LeaderConsensusVerification -> DAGRiderSpecification -> DAGRiderVerification

Naming convention:

| Convention | Description |
| :---       | :--- |
| Init`<Name>`| Initialisation of a state variable |
| `<Name>`Asm | Assumption |
| `<Name>`Inv | Invariant |
| `<Name>`Plt  | Postulate |
| `<Name>`Lem | Lemma |
| `<Name>`Set | Set |
| `<Name>`Thm | Theorem |
| `<Name>`Type | Type definition of a state variable |
| Num`<Name>` | Cardinality |
