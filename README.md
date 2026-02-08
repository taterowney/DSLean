# DSLean: A Bi-directional Interface Between Lean 4 and External Languages

`DSLean` aims to provide a powerful and intuitive interface for communication between the Lean theorem prover and arbitrary DSLs, solvers, and languages. Given a specification of an external language and each component's Lean equivalent, `DSLean` automatically translates back and forth between syntatically correct expressions and type-correct Lean objects. No messing around with the trivialities of parsing and elaboration is required. 

## Quick Start (Docker, recommended)

Pull and run the prebuilt image:

```bash
docker pull ghcr.io/taterowney/dslean:main
docker run --rm -it ghcr.io/taterowney/dslean:main
```

Inside the container:

```bash
./scripts/docker-smoke.sh
```

This image includes Lean (from `lean-toolchain`), Gappa, SageMath, and Macaulay2.

## Local Docker Build

```bash
docker build -t dslean-demo .
docker run --rm -it dslean-demo
```

Or with Compose:

```bash
docker compose run --rm dslean
```

## Native Installation (without Docker)

This project uses Lean 4.27.0:

```bash
lake exe cache get
lake build DSLean.Demos
```

If you want solver-backed tactics, install:
- [Gappa](https://gitlab.inria.fr/gappa/gappa)
- [SageMath](https://doc.sagemath.org/html/en/installation/)
- [Macaulay2](https://www.macaulay2.com/Downloads/)

Then configure runtime paths via environment variables (optional if using defaults):

```bash
export DSLEAN_GAPPA_BIN=/usr/bin/gappa
export DSLEAN_SAGE_BIN=/usr/bin/sage
export DSLEAN_M2_BIN=/usr/bin/M2
export DSLEAN_TMP_DIR=/tmp/dslean
```
