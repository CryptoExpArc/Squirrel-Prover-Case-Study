# Project

## Table of Contents

- [1. Secrecy Verification of Handshake Protocol using Squirrel Prover](#1-secrecy-verification-of-handshake-protocol-using-squirrel-prover)
- [2. Implementation and Analysis of Custom Merkle-Damgård Hash Function](#2-implementation-and-analysis-of-custom-merkle-damgård-hash-function)

## 1. Secrecy Verification of Handshake Protocol using Squirrel Prover

This project presents a new formal verification case study of simplified handshake protocol and examines the usability of Squirrel Prover. It is an evaluation of the practicality of applying Squirrel's existing framework to protocol verification in a post-quantum setting.

The simplified handshake protocol
<img width="844" height="328" alt="Handshake Protocol" src="https://github.com/user-attachments/assets/826e3615-cc01-45ba-b172-21441759137f" />



### Project Objectives:

* Model a simple handshake protocol in Squirrel.
* Define secrecy properties for protocol participants.
* Construct symbolic model and computational proofs of secrecy.
* Analyze proof under the real and ideal projection system.
* Documents practical observations on proof automation, index management, auxiliary lemma development and proof scalability.


### Strengths of Squirrel Prover

Squirrel Prover makes a significant step toward bridging symbolic verification techniques and computational cryptography within a single proof framework, adapting protocol verification to the post-quantum setting.

* Expressive modeling language for symbolic protocols.
* Support for equivalence and Reachability in proof.
* Interactive verification through tactics and trace.
* Strong support for post-quantum computational soundness.

<img width="1674" height="740" alt="image" src="https://github.com/user-attachments/assets/e86ae2c3-f189-42b7-9733-26069905c587" />

Compare CryptoVerif and EasyCrypt with Squirrel since all of them provide guarantees in computational model. CryptoVerif use predefinded primitives Stateful protocols. This makes it fast to use, but sometimes less flexible for new primitives. EasyCrypt is more details and expressive so that it is overhead in modelling and more suite for properties of primitives. Except for EasyCrypt, the other two support stateful protocols' verification. The use of process algebra is inconvenient for interactive protocols. On automation, Squirrel lies in the middle and it is the first completely mechanized proofs of protocols using the CCSA approach. And then, CryptoVerif uses indistinguishability-based oracle access to simulate the adversary's behaviour. EasyCrypt relies on proof framework. Squirrel relies on frame and traces and bi-process equivalences to reason about adversary knowledge and behavior. In hard-coded cryptographic hypothesis, it requires non-trivial syntactic checks and need to compute or analysis subterms. Finally, about post-quantum support, EasyCrypt and Squirrel mainly use EasyPQC and PQ-BC adapt to PQ world. Currently, Squirrel has been used to verify a wide range of protocols. The proofed security properties focus on authentication, unlinkability, secrecy and anonymity. An important trend is that Squirrel not only supports symbolic model, but also extend to computational and post-quantum reasoning.


### Technologies - Logic & Formal Verification with Reachability and Equivalence properties

<img width="1549" height="875" alt="image" src="https://github.com/user-attachments/assets/ea736244-4527-4ade-8055-4183c7165582" />

CCSA is the basic logic, this method relies on the specification of what the adversary cannot do and provides computational complete to symbolic model. The major logic is meta-logic and extend to higher-order indistinguishability logic later. It makes Squirrel support to operate stateful protocol and implement Mechanized proof. Extended PQ-BC logic adapt Squirrel to post-quantum and definded some usable PQ-BC axioms from assumptions.
 
<img width="1719" height="744" alt="image" src="https://github.com/user-attachments/assets/b5fa3395-6c42-4073-a511-77f785fde0c3" />

Logic support Squirrel to structure verification work, and there are four components during verification. Declaration define some messages and different kinds of function symbols we will use in modelling. 

The Protocol process models the communication behavior between protocol agents and then records execution traces for further analyze. 

The Squirrel Prover also involves reachability and equivalence properties. Reachability properties reason about whether an adversary can obtain goals in all protocol traces. It often use timestamps, actions, and trace to describe. For example, the weak secrecy property need to prove that the adversary can obtain secret from frame `frame@t` is false. The `frame@t` contains all outputs observable before and up to `t`, representing the knowledge or available information of adversary.

Equivalence properties more focus on the equivalence between a real system and an ideal system. The real and ideal systems are projections of the Protocol. To be more specific, the real system models the actual protocol, while the ideal system represents a perfectly secure version of the protocol. Instead of proving directly that an adversary cannot obtain a secret, Squirrel Prover proves that the adversary cannot distinguish interactions with the real system from interactions with the ideal system. If the two systems are indistinguishable, the desired security property follows under the corresponding computational assumptions.


### Results

The verification demonstrates that the modeled protocol satisfies the specified secrecy property under the symbolic adversary model. After `set postQuantumSound = true`, the secrecy property of this case study remained valid. This switch provides straightforward between classical and post-quantum environment in Squirrel Prover. However, the attempt at verification of secrecy under the real/ideal system was unsuccessful. The complexity of equivalent reasoning in this setting was increases. In addition, induction over protocol traces and index management challenges may obstructed the completion of the verification. These results both demonstrate the capabilities of Squirrel Prover in computational complete and the current challenges under real/ideal system.


### Discussion and Future Work

During the verification of the real/ideal system proof, it observed that there are some limitations in automated tactics, such as actions became increasingly complex. In addition, error messages generated by automated tactics were often insufficiently detailed and difficult to pinpoint the source of failure. Automated tactics, such as `auto`, in case study was failed to resolve name and index matching problem, while debugging process, the message also failed to clearly indicate the main reason. These findings indicate that improving the usability of proof development could be future research. Researchers could also evaluate Squirrel Prover on more complex protocols and security properties, such as TLS protocol and forward secrecy property.


### Academic Context

This project was a Capstone Project in my last year of master degree(July 2025).

Squirrel Prover Reference: https://squirrel-prover.github.io/



## 2. Implementation and Analysis of Custom Merkle-Damgård Hash Function

<img width="687" height="233" alt="image" src="https://github.com/user-attachments/assets/77a9950f-e4c9-4537-ba90-734c5926a4c3" />


Research Nostradamus attack(Stuck on diamond tree)




