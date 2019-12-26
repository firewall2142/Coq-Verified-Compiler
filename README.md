# Verified Imp compiler for storeless machine

This repository contains a verfied compiler with proofs of terminating conditions for [Imp Language]() for storeless machine (the variables are stored in stack instead).

####Files

* `Compiler.v`  :   Compiler functions, proofs of correctness and termination
* `Facts.v`     :   Theorems about functions and inductive types defined in `ImpVM.v` used in other proofs.
* `ImpVM.v`     :   Imp syntax and VM Instruction set
* `Sequences.v` :   Transition relations
