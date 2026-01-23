import ExternalComputationsInLean.LeanToExternal.Main
import ExternalComputationsInLean.ExternalToLean.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Nat.Basic

open Lean Meta Elab Meta Term Expr Command
open Qq




declare_syntax_cat bijectiveDSLline
syntax (stx+) "<==>" term : bijectiveDSLline

def lineParser : Parser.Parser :=
  Lean.Parser.many1Indent (Lean.Parser.categoryParser `bijectiveDSLline 1)

/-- Declare an external DSL. Lines that follow describe one-to-one correspondences (using `<==>`) between Lean types and external syntax.  -/
syntax (name := bijectiveDSL) "bijective" "external" ident ("(" "numberCast" ":=" term ")")? "where" ppLine lineParser : command

@[command_elab bijectiveDSL]
def bijectiveDSLImpl : CommandElab := fun stx => do
  -- let `(bijective external $name:ident ( numberCast := $castFnStx:term ) where $lines:bijectiveDSLline*) := stx | throwUnsupportedSyntax
  let (name, castFn, lines) ←
    match stx with
    | `(bijective external $name:ident ( numberCast := $castFnStx:term ) where $lines:bijectiveDSLline*) =>
      pure (name, ← liftTermElabM <| elabTerm castFnStx none, lines)
    | `(bijective external $name:ident where $lines:bijectiveDSLline*) =>
      pure (name, q(fun (x:Nat) => x), lines)
    | _ => throwUnsupportedSyntax
  if lines.size == 0 then throwUnsupportedSyntax

  -- let opt : Options := Options.empty.setBool `linter.unused_variables false
  -- modify fun s => { s with maxRecDepth := maxRecDepth.get opt }
  -- modifyScope fun scope => { scope with opts := opt }

  initializeExternalCategory name true true castFn

  let name := name.getId
  for line in lines do
    match line.raw.getArgs.toList with
    | [syntaxPat, _, targetExpr] =>
      let syntaxPats := syntaxPat.getArgs.map .mk
      let target : TSyntax `term := ⟨targetExpr⟩
      declareExternal name syntaxPats target true true {}
    | _ => throwError m!"Unsupported syntax: {line}"



declare_syntax_cat surjectiveDSLline
syntax (stx+) "==>" term (";" Parser.Tactic.optConfig)? : surjectiveDSLline

def lineParserSurj : Parser.Parser :=
  Lean.Parser.many1Indent (Lean.Parser.categoryParser `surjectiveDSLline 1)

/-- Declare an external DSL. Lines that follow describe translations from an external language into Lean (using `==>`).  -/
syntax (name := surjectiveDSL) "surjective" "external" ident ("(" "numberCast" ":=" term ")")? "where" ppLine lineParserSurj : command

@[command_elab surjectiveDSL]
def surjectiveDSLImpl : CommandElab := fun stx => do
  let (name, castFn, lines) ←
    match stx with
    | `(surjective external $name:ident ( numberCast := $castFnStx:term ) where $lines:surjectiveDSLline*) =>
      pure (name, ← liftTermElabM <| elabTerm castFnStx none, lines)
    | `(surjective external $name:ident where $lines:surjectiveDSLline*) =>
      pure (name, q(fun (x:Nat) => x), lines)
    | _ => throwUnsupportedSyntax
  if lines.size == 0 then throwUnsupportedSyntax

  -- let opt : Options := Options.empty.setBool `linter.unused_variables false
  -- modify fun s => { s with maxRecDepth := maxRecDepth.get opt }
  -- modifyScope fun scope => { scope with opts := opt }

  initializeExternalCategory name false true castFn

  let name := name.getId
  for line in lines do
    match line.raw.getArgs.toList with
    | [syntaxPat, _, targetExpr, opts?] =>
      let syntaxPats := syntaxPat.getArgs.map .mk
      let target : TSyntax `term := ⟨targetExpr⟩
      let parsedOptions : ExternalEquivalenceOptions ←
        match opts?.getArgs.toList with
        | [_, options] => elabExternalEquivalenceOptions options
        | _ => pure {}

      declareExternal name syntaxPats target false true parsedOptions
    | _ => throwError m!"Unsupported syntax: {line}"




declare_syntax_cat injectiveDSLline
syntax (stx+) "<==" term : injectiveDSLline

def lineParserInj : Parser.Parser :=
  Lean.Parser.many1Indent (Lean.Parser.categoryParser `injectiveDSLline 1)

/-- Declare an external DSL. Lines that follow describe translations from an external language into Lean (using `==>`).  -/
syntax (name := injectiveDSL) "injective" "external" ident "where" ppLine lineParserInj : command
@[command_elab injectiveDSL]
def injectiveDSLImpl : CommandElab := fun stx => do
  let `(injective external $name where $lines:injectiveDSLline*) := stx | throwUnsupportedSyntax
  if lines.size == 0 then throwUnsupportedSyntax

  -- let opt : Options := Options.empty.setBool `linter.unused_variables false
  -- modify fun s => { s with maxRecDepth := maxRecDepth.get opt }
  -- modifyScope fun scope => { scope with opts := opt }

  initializeExternalCategory name true false q(fun (x:Nat) => x)

  let name := name.getId
  for line in lines do
    match line.raw.getArgs.toList with
    | [syntaxPat, _, targetExpr] =>
      let syntaxPats := syntaxPat.getArgs.map .mk
      let target : TSyntax `term := ⟨targetExpr⟩
      declareExternal name syntaxPats target true false {}
    | _ => throwError m!"Unsupported syntax: {line}"




syntax (name := processExternalCmd) "process" ident term : term
@[term_elab processExternalCmd]
def processExternalCmdImpl : TermElab := fun stx _ => do
  let cat : Name := stx.getArgs[1]!.getId
  let input : String := stx.getArgs[2]!.isStrLit?.get!
  let out ← processExternal cat input
  return out








-- bijective external testlanguage where
--   "Nat" <==> Nat
--   "String" <==> String
--   x "+" y <==> (x:Nat) + y
--   x "*" y <==> (x:Nat) * y
--   x "-" y <==> (x:Nat) - y
--   x "^" y <==> (x:Nat) ^ y
--   "(" x ")" <==> x
--   x "==" y <==> x=y
--   "let" $n ":=" val "in" rest <==> let n := val; rest
--   "fun" $n "->" rest <==> fun n => rest
--   "forall" $n "," rest <==> ∀ n, rest
--   "let" $n ":" ty ":=" bi "in" rest <==> let n:ty := bi; rest
--   "[" x "," y "]" <==> Set.Icc x y
--   x "isin" y <==> x ∈ y
--   "grind" <==> by grind
--   x y <==> (id ∘ x) y
--   "test" <==> "teststring"


-- #eval do
--   let expr ← processExternal `testlanguage "let x : (1 isin [0, 2]) := grind in x"
--   logInfo m!"Elaborated expression: {expr}"

-- theorem test2 : (1) ∈ Set.Icc 0 2 := process testlanguage "let x : (1 isin [0, 2]) := grind in x"
-- #print test2


-- #eval do
--   let expr ← processExternal `testlanguage "let x := fun y -> y + 1 in x 5"
--   logInfo m!"Elaborated expression: {expr}"

-- #eval process testlanguage "let x := fun y -> y + 1 in x 5"








bijective external testlanguage where
  "Nat" <==> Nat
  "String" <==> String
  x "+" y <==> (x:Nat) + y
  x "*" y <==> (x:Nat) * y
  x "-" y <==> (x:Nat) - y
  x "^" y <==> (x:Nat) ^ y
  -- "(" x ")" <==> x
  x "==" y <==> x=y
  -- "let" $n ":=" val "in" rest <==> let n := val; rest
  "fun" $n "->" rest <==> fun n => rest
  "forall" $n "," rest <==> ∀ n, rest
  -- "let" $n ":" ty ":=" bi "in" rest <==> let n:ty := bi; rest
  "[" x "," y "]" <==> Set.Icc x y
  x "isin" y <==> x ∈ y
  "grind" <==> by grind
  -- x y <==> (x : α → β) (y:α)
  -- x y <==> (id ∘ x) y
  "test" <==> "teststring"

-- #eval do
--   let expr ← processExternal `testlanguage "12345"
--   logInfo m!"Elaborated expression: {expr}"

-- #eval do
--   let out ← toExternal `testlanguage q("teststring"="teststring")
--   logInfo m!"External representation: {out}"


#eval do
  logInfo m!"{← Core.betaReduce (q((fun (x:«Nat») => x+1) 5))}"

#eval do
  let m1 ← mkFreshExprMVar none
  let ty : MetaM Expr := mkArrow q(«Nat») q(«Nat»)
  let m2 ← mkFreshExprMVar (some (← ty))
  logInfo m!"{← isDefEq m1 m2}"

  logInfo m!"{(mkApp m1 (.bvar 0)).printdbg} {(← Core.betaReduce <| mkApp m1 (.bvar 0)).printdbg}"
  let e1 ← instantiateMVars <| Expr.lam `testvar q(«Nat») (mkApp m1 (.bvar 0)) .default
  let e2 := Expr.lam `testvar q(«Nat») (.bvar 0) .default
  logInfo m!"e1 : {e1} ({e1.printdbg})"
  logInfo m!"e2 : {e2} ({e2.printdbg})"
  logInfo m!"{← isDefEq e1 e2}"

#eval do
  let m1 ← (mkFreshExprMVar q(«Nat») : TermElabM Expr)

  let e1 := Expr.lam `testvar q(«Nat») m1 .default
  let (e1', newMVarIds) ← makeMVarsDependent e1 [m1.mvarId!]
  logInfo m!"{newMVarIds.toList}"

  -- logInfo m!"Body is {(match e1' with | .lam _ _ body _ => body | _ => panic! "").mvarId!}"

  let e2 := Expr.lam `testvar q(«Nat») (.bvar 0) .default
  logInfo m!"e1 : {e1} ({e1.printdbg})"
  logInfo m!"e1' : {e1'} ({e1'.printdbg})"
  logInfo m!"e2 : {e2} ({e2.printdbg})"
  logInfo m!"{← isDefEq e1' e2}"


#eval do
  let out ← toExternal `testlanguage q(forall (testvar:«Nat»), testvar=testvar)
  logInfo m!"External representation: {out}"

-- #eval do
--   let out ← toExternal `testlanguage (.forallE `testvar q(«Nat») q(1=1) .default)
--   logInfo m!"{q(∀ (x:«Nat»), 1=1)}"
--   logInfo m!"External representation: {out}"

#eval do
  let out ← toExternal `testlanguage q(fun (testvar:«Nat») => testvar)
  logInfo m!"External representation: {out}"


-- #eval do
--   let out ← toExternal `testlanguage q(fun (x:«Nat») => "teststring")
--   logInfo m!"External representation: {out}"


/-TODO:
- No-ops on the Lean side create an infinite loop when translating downwards (e.g. infinite parentheses)
- Doing let ... := val when val's type of the metavariable somehow gets rid of the info about the metavariable.
- Custom parser states
- Non-ascii characters ok?
- Wildcards/optional within patterns correspond to lists on the other side?
- Could we skip the entire elaboration step by just looking at the SyntaxNodeKind?
- Backtracking (in parsing too) for type filtration?
- Typechecking target expressions, maybe some theorems about correctness/roundtripability?
- Better logic for `num`s
- Why no antiquot at the beginning of a line?
- Do unassigned types default to Nat too much?
-/
