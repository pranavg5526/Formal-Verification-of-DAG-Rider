# Formal Verification of DAG-Rider

There is a trend in blockchains to switch to DAG-based consensus protocols to decrease their energy footprint and improve security. A DAG-based consensus protocol orders transactions for securing blocks, and relies on built-in fault tolerance communications via Byzantine Atomic Broadcasts. The ubiquity and strategic importance of blockchains call for formal proof of their correctness. We formalize the DAG-based consensus protocol called DAG-Rider in TLA+ and prove the safety properties with the TLA+ proof system. 

The formalization requires a refinement approach for modelling the consensus. In an abstracted model (LeaderConsensus), we first show the safety of DAG-based consensus on leaders and then further refine the specification to encompass all messages for all processes (DAGRider). Overall the specification consists of 683 (with comments) number of lines, and the proof system verifies 1922 obligations in approx. 5 minutes.

Naming convention:

<Name>Asm => Assumption

<Name>Plt => Postulate

<Name>Lem => Lemma

<Name>Thm => Theorem

<Name>Type => Type definition of a state variable

Init<Name> => Initialisation of a state variable

