# DSLean: A Bi-directional Interface Between Lean 4 and External Languages

`DSLean` aims to provide a powerful and intuitive interface for communication between the Lean theorem prover and arbitrary DSLs, solvers, and languages. Given a specification of an external language and each component's Lean equivalent, `DSLean` automatically translates back and forth between syntatically correct expressions and type-correct Lean objects. No messing around with the trivialities of parsing and elaboration is required. 


### Installation

This project uses Lean 4.27.0. Make sure Lean is installed, then run:

```bash
lake exe cache get
lake build
```

Or include as a library:
```toml
[[require]]
name = "DSLean"
git = "https://github.com/taterowney/DSLean.git"
```

Additionally, depending on which tactics you may want to use, you'll want to install the following external solvers:
 - [Gappa](https://gitlab.inria.fr/gappa/gappa)
 - [SageMath](https://doc.sagemath.org/html/en/installation/)
 - [Macaulay2](https://www.macaulay2.com/Downloads/)

Make sure the default commands to run these programs are available in your environment (`gappa`, `sage`, `macaulay2`), or specify an installation to use by setting the `DSLEAN_GAPPA_PATH`, `DSLEAN_SAGE_PATH`, and/or `DSLEAN_M2_PATH` environment variables (e.g. by adding `export DSLEAN_GAPPA_PATH=/path/to/gappa/executable` to your `.bashrc` file or equivalent). 

