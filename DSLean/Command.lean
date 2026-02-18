import DSLean.ExternalToLean.Main
import DSLean.LeanToExternal.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Nat.Basic

open Lean Meta Elab Meta Term Expr Command
open Qq




declare_syntax_cat bijectiveDSLline
syntax (stx+) "<==>" term (";" Parser.Tactic.optConfig)? : bijectiveDSLline

def lineParser : Parser.Parser :=
  Lean.Parser.many1Indent (Lean.Parser.categoryParser `bijectiveDSLline 1)

/-- Declare an external DSL. Lines that follow describe one-to-one correspondences (using `<==>`) between Lean types and external syntax.  -/
syntax (name := bijectiveDSL) "external" ident ("(" "numberCast" ":=" term ")")? "where" ppLine lineParser : command

@[command_elab bijectiveDSL]
def bijectiveDSLImpl : CommandElab := fun stx => do
  let (name, castFn, lines) ←
    match stx with
    | `(external $name:ident ( numberCast := $castFnStx:term ) where $lines:bijectiveDSLline*) =>
      pure (name, some <| ← liftTermElabM <| elabTerm castFnStx none, lines)
    | `(external $name:ident where $lines:bijectiveDSLline*) =>
      pure (name, none, lines)
    | _ => throwUnsupportedSyntax
  if lines.size == 0 then throwUnsupportedSyntax

  initializeExternalCategory name true true castFn

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
      declareExternal name syntaxPats target true true parsedOptions
    | _ => throwError m!"Unsupported syntax: {line}"



declare_syntax_cat surjectiveDSLline
syntax (stx+) "==>" term (";" Parser.Tactic.optConfig)? : surjectiveDSLline

def lineParserSurj : Parser.Parser :=
  Lean.Parser.many1Indent (Lean.Parser.categoryParser `surjectiveDSLline 1)

/-- Declare an external DSL. Lines that follow describe translations from an external language into Lean (using `==>`).  -/
syntax (name := surjectiveDSL) "external" ident ("(" "numberCast" ":=" term ")")? "where" ppLine lineParserSurj : command

@[command_elab surjectiveDSL]
def surjectiveDSLImpl : CommandElab := fun stx => do
  let (name, castFn, lines) ←
    match stx with
    | `(external $name:ident ( numberCast := $castFnStx:term ) where $lines:surjectiveDSLline*) =>
      pure (name, some <| ← liftTermElabM <| elabTerm castFnStx none, lines)
    | `(external $name:ident where $lines:surjectiveDSLline*) =>
      pure (name, none, lines)
    | _ => throwUnsupportedSyntax
  if lines.size == 0 then throwUnsupportedSyntax

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
syntax (stx+) "<==" term (";" Parser.Tactic.optConfig)? : injectiveDSLline

def lineParserInj : Parser.Parser :=
  Lean.Parser.many1Indent (Lean.Parser.categoryParser `injectiveDSLline 1)

/-- Declare an external DSL. Lines that follow describe translations from Lean to an external language (using `<==`).  -/
syntax (name := injectiveDSL) "external" ident "where" ppLine lineParserInj : command
@[command_elab injectiveDSL]
def injectiveDSLImpl : CommandElab := fun stx => do
  let `(external $name where $lines:injectiveDSLline*) := stx | throwUnsupportedSyntax
  if lines.size == 0 then throwUnsupportedSyntax

  initializeExternalCategory name true false none

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
      declareExternal name syntaxPats target true false parsedOptions
    | _ => throwError m!"Unsupported syntax: {line}"
