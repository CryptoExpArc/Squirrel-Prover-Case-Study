# Research Project

## Table of Contents

- [1. Secrecy Verification of Handshake Protocol using Squirrel Prover](#1-secrecy-verification-of-handshake-protocol-using-squirrel-prover)
  - [Project Objectives](#project-objectives)
  - [Strengths of Squirrel Prover](#strengths-of-squirrel-prover)
  - [Technologies - Logic & Formal Verification with Reachability and Equivalence properties](#technologies---logic--formal-verification-with-reachability-and-equivalence-properties)
  - [Results](#results)
  - [Discussion and Future Work](#discussion-and-future-work)
  - [Academic Context](#academic-context)
- [2. Implementation and Analysis of Custom Merkle-Damgård(MD) Hash Function](#2-implementation-and-analysis-of-custom-merkle-damgård(md)-hash-function)
  - [Custom MD Hash Function Overview and Results](#custom-md-hash-function-overview-and-results)
  - [Function Discussion and Future Work](#function-discussion-and-future-work)

## 1. Secrecy Verification of Handshake Protocol using Squirrel Prover

This project presents a formal verification case study of a simplified handshake protocol and examines the usability of Squirrel Prover. It evaluates the practicality of applying Squirrel's existing framework to protocol verification in a post-quantum setting.

The simplified handshake protocol
<img width="844" height="328" alt="Handshake Protocol" src="https://github.com/user-attachments/assets/826e3615-cc01-45ba-b172-21441759137f" />


### Project Objectives

* Model a simple handshake protocol in Squirrel.
* Define secrecy properties for protocol participants.
* Construct a symbolic model and computational proofs of secrecy.
* Analyze proofs under the real and ideal projection systems.
* Document practical observations on proof automation, index management, auxiliary lemma development and proof scalability.


### Strengths of Squirrel Prover

<img width="1674" height="740" alt="image" src="https://github.com/user-attachments/assets/e86ae2c3-f189-42b7-9733-26069905c587" />

It is necessary to compare CryptoVerif, EasyCrypt, and Squirrel. Three of them aim to provide guarantees in the computational model. 

CryptoVerif uses predefined primitives and supports stateful protocols. This makes it fast to use, but sometimes less flexible for new primitives. EasyCrypt is more detailed and expressive, which can introduce additional modeling overhead but makes it well suited to reasoning about properties of primitives. Unlike EasyCrypt, both CryptoVerif and Squirrel support verification of stateful protocols. The use of process algebra can be inconvenient for highly interactive protocols. 

In terms of automation, Squirrel lies between the other two tools and is the first framework to provide completely mechanized protocol proofs using the CCSA approach. CryptoVerif uses indistinguishability-based oracle access to simulate adversary behavior, whereas EasyCrypt relies on a proof-oriented framework. Squirrel reasons about adversary knowledge and behavior through frames, traces and equivalence. Regarding hard-coded cryptographic hypotheses, verification often requires non-trivial syntactic checks and analysis of subterms. 

Finally, for post-quantum support, EasyCrypt and Squirrel can be combined with EasyPQC and PQ-BC style reasoning to adapt to the post-quantum setting. Squirrel has already been used to verify a wide range of protocols, including properties such as authentication, unlinkability, secrecy and anonymity. An important trend is that Squirrel not only supports symbolic modeling but also extends to computational and post-quantum reasoning.

Overall, Squirrel Prover makes a significant step toward bridging symbolic verification techniques and computational cryptography within a single proof framework, thereby adapting protocol verification to the post-quantum setting.

* Expressive modeling language for symbolic protocols.
* Support for equivalence and Reachability in proof.
* Interactive verification through tactics and trace.
* Strong support for post-quantum computational soundness.


### Technologies - Logic & Formal Verification with Reachability and Equivalence properties

<img width="1549" height="875" alt="image" src="https://github.com/user-attachments/assets/ea736244-4527-4ade-8055-4183c7165582" />

CCSA is the basic or underlying logic. It relies on specifying what the adversary cannot do and provides computational soundness for the symbolic model. The framework is based on a meta-logic and can be extended to higher-order indistinguishability reasoning. This allows Squirrel to reason about stateful protocols and support mechanized proofs. The extended PQ-BC logic adapts Squirrel to the post-quantum setting and defines usable PQ-BC axioms from cryptographic assumptions.
 
<img width="1719" height="744" alt="image" src="https://github.com/user-attachments/assets/b5fa3395-6c42-4073-a511-77f785fde0c3" />

Logic support Squirrel to structure verification work, and there are four components during verification. Declaration define some messages and different kinds of function symbols we will use in modelling. 

The Protocol process models the communication behavior between protocol agents and then records execution traces for further analyze. 

The Squirrel Prover also involves reachability and equivalence properties. Reachability properties reason about whether an adversary can obtain a target value in any protocol trace. They often use timestamps, actions, and traces to describe protocol executions. For example, the weak secrecy property proves that the adversary cannot derive the secret from the frame `frame@t`. The `frame@t` contains all outputs observable before and up to time `t`, representing the knowledge available to the adversary at that point.

Equivalence properties more focus on the equivalence between a real system and an ideal system. The real and ideal systems are projections of the Protocol. To be more specific, the real system models the actual protocol, while the ideal system represents a perfectly secure version of the protocol. Instead of proving directly that an adversary cannot obtain a secret, Squirrel Prover proves that the adversary cannot distinguish interactions with the real system from interactions with the ideal system. If the two systems are indistinguishable, the desired security property follows under the corresponding computational assumptions.


### Results

The verification demonstrates that the modeled protocol satisfies the specified secrecy property under the symbolic adversary model. After `set postQuantumSound = true`, the secrecy property of this case study remained valid. This switch provides straightforward between classical and post-quantum environment in Squirrel Prover. However, the attempt at verification of secrecy under the real/ideal system was unsuccessful. The complexity of equivalence reasoning in this setting was increases. In addition, induction over protocol traces and index management challenges may have obstructed the completion of the verification. These results both demonstrate the capabilities of Squirrel Prover in computational complete and the current challenges under real/ideal system.


### Discussion and Future Work

During the verification of the real/ideal system proof, there are some limitations in automated tactics, such as actions became increasingly complex. In addition, error messages generated by automated tactics were often insufficiently detailed and difficult to pinpoint the source of failure. Automated tactics, such as `auto`. In this case study, the verification returned false when attempting to resolve the name and index matching problem. while debugging process, the message also failed to clearly indicate the main reason. These findings indicate that improving the usability of proof development could be future research. Researchers could also evaluate Squirrel Prover on more complex protocols and security properties, such as TLS protocol and forward secrecy property.


### Academic Context

This project was a capstone project in my last year of master's degree(July 2025).

Squirrel Prover Reference: https://squirrel-prover.github.io/



## 2. Implementation and Analysis of Custom Merkle-Damgård Hash Function

### Custom MD Hash Function Overview and Results

i) Deal with the input message: vector<string> split(string message)

Split message, each 12 bits as a block for Merkle-Damg ard and custom hash

If the last block is less than 12 bits, then add padding block "0"

ii) The non-trivial custom hash: `string customHash(string temp, string last_result)`

The input has 24 bits: 12 bits (splitted message) + 12 bits (iv or last result)

Split the input again, make each 4 bits as a block

nonlinear S-box:

According to S-box, replace the value of each block

<img width="675" height="91" alt="image" src="https://github.com/user-attachments/assets/21cca918-f894-452b-b5be-948858906032" />

  Eg. Block: 1010
  
  In decimal, the block is 2^3 + 2^1 = 8 + 2 = 10
  
  Replace it to the output 4, and the binary of 4 is 0100
  
After replace all the block, combine these outputs as a new 24 bits message.

In code, name the new 24 bits message as `dec_bt_24` or `after_S_box`.

Bitwise operations:

The rule of bitwise operations depends on the reminder of decimal number `dec_bt_24`, ie. `dec_bt_24%3`

Add obj as random seed into the rule of bitwise operations

Each bit should be operated, then the result is `hash_value_24` or `after_S_box_bit`

The result has 24 bits, so it still needs to be split

Split depends on the reminder of decimal number `hash_value_24`, ie: `dec_after_S_box_bit%2`

iii) Merkle-Damg ard-based hash function H: string MD_H(string m)

split(m): split message function

MD_round: the number of Merkle-Damg ard unit

1^st round/unit: customHash(splitted message m0, iv)

2^nd round/unit: customHash(splitted message m1, last result)

Last round/unit: customHash(splitted message m || PB, last result) = final hash value

iv) Find collision: string collision(string message)

Burte force: try the integer number from 2^23 - 1 to 2^24 - 1

`MD_H(test_message) == MD_H(given message)`

Avalanche effect: not strict avalanche criterion (SAC).

`vector<int> record_2_MD_custom_hash_values_test_sub_avalanche_effect(string hash_value1, string hash_value2)`

`void avalanche_effect()`

The partial output of Q2 c++ code:

total test: 10000

The effect of bit 1: 0.6544

The effect of bit 2: 0.6194

The effect of bit 3: 0.5689

The effect of bit 4: 0.5915

The effect of bit 5: 0.5536

The effect of bit 6: 0.5767

The effect of bit 7: 0.5563

The effect of bit 8: 0.6079

The effect of bit 9: 0.603

The effect of bit 10: 0.668

The effect of bit 11: 0.6332

The effect of bit 12: 0.4426

Iterative experiments on round numbers determined 5 to 7 rounds as the optimal range and excessive iterations caused the over-diffusion phenomenon.

### Function Discussion and Future Work

Research Nostradamus attack(Stuck on diamond tree)





