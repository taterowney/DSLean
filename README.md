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


### Making a DSL

DSLean's `external` command specifies equivalences between Lean types and external syntax:

```lean
external myDSL where
    "yep" <==> True
    "nope" <==> False

#check fromExternal myDSL "yep" -- True

#eval do logInfo <|
  ← fromExternal' `myDSL "yep" -- True (but as an Expr)

#eval toExternal `myDSL (q(«False»)) -- "nope"
```

More complicated syntax containing "blanks" can also be specified:

```lean
external myNewDSL where
    "zero" <==> 0
    "successor" n <==> Nat.succ n

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

