# Formal Verification of DAG-Rider

There is a trend in blockchains to switch to DAG-based consensus protocols to decrease their energy footprint and improve security. A DAG-based consensus protocol orders transactions for securing blocks, and relies on built-in fault tolerance communications via Byzantine Atomic Broadcasts. The ubiquity and strategic importance of blockchains call for formal proof of their correctness. We formalize the DAG-based consensus protocol called DAG-Rider in TLA+ and prove the safety properties with the TLA+ proof system. 

The formalization requires a refinement approach for modelling the consensus. In an abstracted model (LeaderConsensus), we first show the safety of DAG-based consensus on leaders and then further refine the specification to encompass all messages for all processes (DAGRider). Overall the specification consists of 683 (with comments) number of lines, and the proof system verifies 1922 obligations in approx. 5 minutes.

A common approach to formally model procedural code in TLA+ is to specify a discrete transition system whose traces correspond to possible executions of the code. 
The naive translation from the pseudo-code (by setting every variable from the protocol, including a variable for each process's current line number, to be a variable in the specification) into a TLA+ specification is not viable. This model, while direct, is very fine-grained, rendering the proofs of properties of interest extremely tedious.

To obtain a more succinct and tractable model, we employ several abstraction techniques: they remove unnecessary details and produce a specification that is amenable to proofs. First, we employ a procedural abstraction that ignores all states that are internal to a procedure and only represents the input/output behaviour of each procedure in the DAG-Rider protocol. For instance, in the  $\mathit{wave\_ready}$ procedure of [1], the relevant variables  are $\mathit{decidedWave}$, $\mathit{deliveredVertices}$, $\mathit{leadersStack}$, but not the loop variable $w'$ or the auxiliary variable $v'$. 
Second, because we focus on safety properties, we remove component features that are only required for liveness and have no impact on the safety proof. For instance, random coin tosses can be replaced with deterministic ones.
Third, we use memoization to efficiently compute the values taken by recursive functions, by introducing a fresh state variable that stores the needed information to evaluate recursive functions in a single step.
Finally, we separate the concerns and break the safety property into two, namely (1) consistent communication and (2) consistent leader election. For (1) we model the DAG-construction and show that the causal histories agree for a same vertex in the DAG of two different processes, and that there is no equivocation of blocks by faulty processes. For (2), we model the consensus protocol and prove that the same leaders are elected and in the same order. To obtain a complete yet simple model of the consensus protocol, we observe that it only needs reachablity information associated with wave leader vertices to commit leaders, and therefore abstract the content of DAG into the so-called leaderReachablity record. We combine consensus protocol specifications in DAG construction specifications to obtain the one of DAG-Rider protocol. 

Given our faithful specification of DAG-Rider in TLA+, we prove its expected safety properties by identifying invariants and proving them within TLA-PS. When using TLA-PS and similar proof systems, the most challenging task is to come up with relevant inductive invariants (that hold initially and are preserved when taking transitions). For DAG-Rider, to prove the consistency of communication during the DAG construction we identified 6 new invariants, and to prove the consistency of leader election we identified 10 new invariants. We prove some these invariants independntly while others with the assumption of already proven invariants.


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
