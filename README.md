# Coq proof for the equivalence of semantics defined on an interaction language with concurrent regions

This repository hosts a proof written in the Gallina language.
We use the Coq automated theorem prover to prove the 
equivalence of a denotational and an operational semantics over a formal language of "interactions".

A previous version of the proof can be found
[here](https://github.com/erwanM974/coq_hibou_label_semantics_equivalence).

In this new version:
- we introduce a co-region operator which makes the language more expressive
- we slighlty reformulate the operational semantics using fewer predicates

"Interactions" model the behavior of distributed systems and can be considered to be a
formalisation of UML Sequence Diagrams.

A web page (generated with coqdoc) presenting the proof can be accessed 
[here](https://erwanm974.github.io/coq_interaction_semantics_equivalence_with_coregions/).

An associated tool for manipulating interaction models is available on 
[this repository](https://github.com/erwanM974/hibou_label).