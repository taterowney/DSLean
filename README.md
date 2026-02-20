# DSLean: A Bi-directional Interface Between Lean 4 and External Languages

`DSLean` aims to provide a powerful and intuitive interface for communication between the Lean theorem prover and arbitrary DSLs, solvers, and languages. Given a specification of an external language and each component's Lean equivalent, `DSLean` automatically translates back and forth between syntatically correct expressions and type-correct Lean objects. No messing around with the trivialities of parsing and elaboration is required. 


### Quick Start (Docker)

To try out DSLean, we provide a Docker image which bundles Lean, Gappa, SageMath, and Macaulay2 so you don't need to install anything yourself.

**Option A — VS Code Dev Container (recommended):**
1. Install [Docker](https://www.docker.com/) and the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) VS Code extension.
2. Open this repository in VS Code.
3. When prompted, click **"Reopen in Container"** (or run the command `Dev Containers: Reopen in Container` from the command palette).
4. Wait for the container to build — this will install all dependencies and run `lake build`. The first build takes a while since it pulls Mathlib, but subsequent opens are fast.
5. Once the build finishes, open any `.lean` file (e.g. `DSLean/TacticExamples.lean`) and the Lean 4 extension will work out of the box.

**Option B — Plain Docker:**
```bash
docker build -t dslean .
docker run -it dslean
```

> **Note:** The image is large (~several GB) due to SageMath and Mathlib. The first build will take some time.

### Manual Installation

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


### Making a DSL

DSLean's `external` command specifies equivalences between Lean types and external syntax:

```lean
external myDSL where
    "yep" <==> True
    "nope" <==> False

#check fromExternal myDSL "yep" -- True

#eval fromExternal' `myDSL "yep" -- True (but as an Expr)

#eval toExternal' `myDSL (q(False)) -- "nope"
```

The translation functions `fromExternal` and `toExternal` elaborate everything automatically, while `fromExternal'` and `toExternal'` work directly with `Expr`s at the meta level and will probably be helpful when making tactics and such. 

More complicated syntax containing "blanks" can also be specified:

```lean
external myNewDSL where
    "zero" <==> 0
    "successor_of" n <==> Nat.succ n

#eval fromExternal myNewDSL "successor_of zero" -- 1
```

This will work polymorphically as much as possible:

```lean
external myWeirdDSL where
    "one" <==> (1:Nat)
    "one_but_int" <==> (1:Int)
    x "plus" y <==> x + y

#eval fromExternal myWeirdDSL "one plus one" -- (2 : ℕ)
#eval fromExternal myWeirdDSL "one_but_int plus one_but_int" -- (2 : ℤ)
```

You can also share variable names across the DSL. Simply put a `$` before something intended to represent a variable name when it appears on the lefthand side:

```lean
external myBetterDSL where
    "declare" $name "=" val "(" type ");" rest <==> let name : type := val; rest
    "nat" <==> ℕ

#check fromExternal myBetterDSL "declare myvar = 5 (nat); myvar" -- let myvar : ℕ := 5; myvar
```

As you can probably see above, DSLean automatically handles translation of number literals (for the sake of performance). By default they're translated to `Nat`s; if you want something else, just specify it with a conversion from `Nat` to it:

```lean
external myIntegerDSL (numberCast := Int.ofNat) where
    "declare" $name "=" val "(" type ");" rest <==> let name : type := val; rest
    "int" <==> ℤ
    "-" x <==> -x

#check fromExternal myIntegerDSL "declare myvar = -5 (int); myvar" -- let myvar : ℤ := -5; myvar
```
(This solution is kind of janky, I'm working on making it more intuitive)

There are also some translations that can only be performed in one direction. For example, something like...

```lean
external myOneWayDSL where
    "getFirst" a b c ==> a

#check fromExternal myOneWayDSL "getFirst 1 2 3" -- 1
```
...can be expressed, even though the translation from `a` back to the original syntax can't be accomplished since the values of `b` and `c` would be ambiguous. This is also particularly helpful when specifying equivalences such as parentheses to indicate precedence: it's perfectly valid to add more parentheses around an expression forever since its value never changes (DSLean will generally try to avoid doing this if there are other options for ways to parse the expression, but infinite loops may occur if those aren't available). 

One-way equivalences the other way can also be made with `<==`. 

⚠⚠⚠ IMPORTANT: due to what appears to be a bug in Lean, keywords defined as part of an external syntax may also randomly be registered as a keyword within Lean, preventing one from accessing declarations of the same name (for example, the equivalence `"yep" <==> True` may cause `yep` to be a keyword, and something like `def yep := 1 #check yep` will fail). This problem occurs very inconsistently, and happens despite correct scoping of the syntax declarations in `DSLean.ExternalToLean.Parsing`. To get around this, wrap identifiers in "«...»" (e.g. `«yep»`) to be able to access them. 

### Navigating the Code

The `DSLean` folder contains examples in `UsageExamples.lean` and `TacticExamples.lean`, as well as the implementations of three example tactics in `Gappa.lean`, `Desolve.lean`, and `LeanM2.lean`. The entry point to DSLean's functionality is defined in `Command.lean`. The core algorithms for translating from Lean expressions to external syntax, and from external syntax back to Lean, are found in `DSLean/LeanToExternal/Main.lean` and `DSLean/ExternalToLean/Main.lean` respectively, with additional functionality around metavariable unification in `DSLean/Utils/Pattern.lean`. 
