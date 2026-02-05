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


def fromExternal := processExternal

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
