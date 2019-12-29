# Verified Imp compiler for storeless machine

This repository defines a compiler from [Imp Language](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html) to a virtual machine using stack for storing variables and proves preservation of semantics of the source program.

### Files

* `Compiler.v`  :   Compiler functions, proofs of correctness on termination
* `Facts.v`     :   Theorems about functions and inductive types defined in `Imp.v` used in other proofs.
* `Imp.v`       :   Imp syntax and VM Instruction set
* `Sequences.v` :   Transition relations
