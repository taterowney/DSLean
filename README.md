# DSLean: A Bi-directional Interface Between Lean 4 and External Languages

`DSLean` aims to provide a powerful and intuitive interface for communication between the Lean theorem prover and arbitrary DSLs, solvers, and languages. Given a specification of an external language and each component's Lean equivalent, `DSLean` automatically translates back and forth between syntatically correct expressions and type-correct Lean objects. No messing around with the trivialities of parsing and elaboration is required. 


### Installation

This project uses Lean 4.27.0. Make sure Lean is installed, then run:

```bash
lake exe cache get
lake build
```

Additionally, depending on which tactics you may want to use, you'll want to install the following external solvers:
 - [Gappa](https://gitlab.inria.fr/gappa/gappa)
 - [SageMath](https://doc.sagemath.org/html/en/installation/)
 - [Macaulay2](https://www.macaulay2.com/Downloads/)

Currently you'll have to modify absolute paths within the files to make these work (TODO fix)