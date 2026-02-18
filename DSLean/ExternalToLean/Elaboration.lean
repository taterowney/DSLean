import Lean
import Std.Internal.Parsec
import Std.Internal.Parsec.Basic
import Std.Internal.Parsec.String
import Lean.Elab.AuxDef
import Qq.Macro
import Lean.Elab.Command
import DSLean.Utils.Pattern
import DSLean.ExternalToLean.Basic
import Lean.Parser.Command
import Lean.Parser.Syntax
import Lean.Parser.Term
import Lean.Elab.Syntax

import Mathlib.Data.Real.Basic -- for definition of Reals

import DSLean.Utils.Syntax
import DSLean.Utils.Datatypes

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq

open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command
open Lean.Elab.Command



/-- Convert a `stx` node into a `macroArg` node for use in `expandMacroArg`. Identifiers, which are usually interpreted as parser categories, will instead be converted to the names of the bound variables, with the category being the supplied name (i.e. `x` => `x:mycategory`). -/
def toMacroArg (stx : TSyntax `stx) (cat : Name) : CommandElabM (TSyntax `Lean.Parser.Command.macroArg) := do
  -- Replace any identifiers (which are treated as parserCategories) with the category `cat`
  let (stx, names) ← TSyntax.findAndReplaceM (fun stx => do
    match stx with
    | Lean.Syntax.node _ `Lean.Parser.Syntax.cat children =>
      match children.toList with
      | (.ident _ name _ _) :: rest =>
        let new_children := (mkIdent cat).raw :: rest
        return some ((Lean.Syntax.node default `Lean.Parser.Syntax.cat new_children.toArray), [name.toName])
      | _ => return none
    | Lean.Syntax.node _ `stx.pseudo.antiquot children =>
      match children.toList with
      | _ :: _ :: (.ident _ name _ _) :: _ =>
        let new_children := [mkIdent cat].toArray
        return some ((Lean.Syntax.node default `Lean.Parser.Syntax.cat new_children), [name.toName])
      | _ => return none
    | _ => return none) stx

  -- Should only be at most one identifier replaced (not sure how there could be multiple anyway)
  if names.length > 1 then throwError "assertion failed"

  -- Wrap to make it into a macroArg; add the identifier if there was one
  match names with
  | [] => return ⟨Lean.Syntax.node default `Lean.Parser.Command.macroArg #[(Lean.Syntax.node default `null #[]), stx.raw]⟩ -- No identifier, just an atom or something
  | _  => return ⟨Lean.Syntax.node default `Lean.Parser.Command.macroArg #[(Lean.Syntax.node default `null #[(mkIdent names[0]!), (Lean.Syntax.atom default ":")]), stx.raw]⟩


/-- Given a category name and an array of `stx` Syntax objects (treated as patterns), add a definition to the environment that matches that pattern (throwing an error otherwise) -/
def declareExternalElaborator (kind : SyntaxNodeKind) (cat : Name) (patterns : Array (TSyntax `stx)) (target : ExternalEquivalenceKey) : CommandElabM Unit := do
  let asMacroArgs ← patterns.mapM (fun a => toMacroArg a cat) -- Convert each of the syntax elements to MacroArgs
  let (_, patArgs) := (← asMacroArgs.mapM expandMacroArg).unzip -- Create antiquoted patterns that match them

  let equiv ← getExternalEquivalence target
  let ⟨vars, binderNames⟩ ← match equiv with
  | none => throwError m!"Internal assertion failed: no external equivalence found for '{target.name}'"
  | some e => pure (e.exprPattern.getVars.toList, e.exprPattern.getBinderVars.toList)

  let vars_stx : List Term ← vars.mapM (fun n => do
    let as_name : TSyntax `term := mkStrLit n.toString
    let as_ident : TSyntax `term := mkIdent n
    `(Prod.mk ($as_name).toName $as_ident)
    )
  let vars_stx_array : TSepArray `term "," := TSepArray.ofElems vars_stx.toArray

  let binders_stx : List Term ← binderNames.mapM (fun n => do
    let as_name : TSyntax `term := mkStrLit n.toString
    let as_ident : TSyntax `term := mkIdent n
    `(Prod.mk ($as_name).toName $as_ident)
    )
  let binders_stx_array : TSepArray `term "," := TSepArray.ofElems binders_stx.toArray

  let pat : TSyntax `term := ⟨mkNode kind patArgs⟩
  let target : TSyntax `term := mkStrLit target.name.toString
  let alts : TSyntaxArray ``matchAlt := #[← `(matchAltExpr| | `($pat) => pure ( ( ⟨($target).toName⟩ : ExternalEquivalenceKey), ([ $vars_stx_array,* ] : List (Name × Syntax)), ([ $binders_stx_array,* ] : List (Name × Syntax)) ) )] -- The core of our match statement. We store the details about what we're elaborating to in an enivonment extension to avoid having to quote everything here.

  let mut k := kind
  if k.isStr && k.getString! == "antiquot" then
    k := k.getPrefix
  if k == choiceKind then
    throwErrorAt alts[0]!
      "invalid alternative, multiple interpretations for pattern (solution: specify node kind using (kind := ...) ...`)"

  -- magic (from Lean.Elab.ElabRules)
  let alts ← alts.mapM fun (alt : TSyntax ``matchAlt) => match alt with
    | `(matchAltExpr| | $pats,* => $rhs) => do
      let pat := pats.elemsAndSeps[0]!
      if !pat.isQuot then
        throwUnsupportedSyntax
      let quoted := getQuotContent pat
      let k' := quoted.getKind
      if checkRuleKind k' k then
        pure alt
      else if k' == choiceKind then
          match quoted.getArgs.find? fun quotAlt => checkRuleKind quotAlt.getKind k with
          | none        => throwErrorAt alt "invalid elab_rules alternative, expected syntax node kind '{k}'"
          | some quoted =>
            let pat := pat.setArg 1 quoted
            let pats := ⟨pats.elemsAndSeps.set! 0 pat⟩
            `(matchAltExpr| | $pats,* => $rhs)
      else
        throwErrorAt alt "invalid elab_rules alternative, unexpected syntax node kind '{k'}'"
    | _ => throwUnsupportedSyntax

  -- Full matcher definition. We register it as a `external_elab` attribute so it can be conveniently found later (without having to mess around at the meta level)
  let attr ← `(attrInstance| $(mkIdent `external_elab):ident $(← mkIdentFromRef k):ident)
  let matcher_def : Syntax ← `(@[$attr]
      public aux_def elabRules $(mkIdent k) : ExternalElabSignature :=
      fun stx _ => match stx with $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)

  elabCommand matcher_def


@[inline] def externalIdentKind (cat : Ident) := Name.str cat.getId "process_ident"
@[inline] def externalNumKind (cat : Ident) := Name.str cat.getId "process_num"
@[inline] def externalScientificKind (cat : Ident) := Name.str cat.getId "process_scientific"



/-- Add default elaborators common to every DSL. TODO: Scientific notation. Also since `num parsing is weird, right now it automatically treats them as Nats. Might be nice to parameterize this. -/
def declareDefaultElaborators (cat : Ident) (checkInjective? : Bool) (checkSurjective? : Bool) (castFn : Option Expr) : CommandElabM Unit := do
  -- using a syntax quotation like `(syntax:1024 ident : $cat) errors for some reason; construct manually
  -- `(syntax:1024 (name := kindNamePlaceholder) ident : catPlaceholder)
  let kindName := externalIdentKind cat
  let identSyntaxDecl : TSyntax `command := .mk (Lean.Syntax.node default `Lean.Parser.Command.syntax #[(Lean.Syntax.node default `null #[]), (Lean.Syntax.node default `null #[]), (Lean.Syntax.node default `Lean.Parser.Term.attrKind #[(Lean.Syntax.node default `null #[])]), (Lean.Syntax.atom default "syntax"), (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.precedence #[(Lean.Syntax.atom default ":"), (Lean.Syntax.node default `num #[(Lean.Syntax.atom default "1024")])])]), (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.Command.namedName #[(Lean.Syntax.atom default "("), (Lean.Syntax.atom default "name"), (Lean.Syntax.atom default ":="), mkIdent kindName, (Lean.Syntax.atom default ")")])]), (Lean.Syntax.node default `null #[]), (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.Syntax.cat #[(mkIdent `ident), (Lean.Syntax.node default `null #[])])]), (Lean.Syntax.atom default ":"), cat])
  elabCommand identSyntaxDecl -- identifiers are part of any DSL. How they are declared/managed is defined by the language in question.

  let pat ← liftTermElabM <| (Expr.fvar ⟨`ident⟩).toPattern #[] #[`ident]
  addExternalEquivalence kindName cat.getId kindName pat #[.node default `Lean.Parser.Syntax.cat #[(mkIdent `ident), (Lean.Syntax.node default `null #[])]] checkInjective? checkSurjective?

  let target : TSyntax `term := mkStrLit kindName.toString
  let attr ← `(attrInstance| $(mkIdent `external_elab):ident $(← mkIdentFromRef kindName):ident)
  let matcher_def : Syntax ← `(@[$attr]
      public aux_def elabRules $(mkIdent kindName) : ExternalElabSignature :=
      fun stx _ => match stx.getArg 0 with | Syntax.ident _ _ _ _ => pure ( ( ⟨($target).toName⟩ : ExternalEquivalenceKey), ([] : List (Name × Syntax)), ([(`ident, stx.getArg 0)] : List (Name × Syntax)) ) | _ => no_error_if_unused% throwUnsupportedSyntax)
  elabCommand matcher_def


  let kindName := externalNumKind cat
  let numSyntaxDecl : TSyntax `command := .mk (Lean.Syntax.node default `Lean.Parser.Command.syntax #[(Lean.Syntax.node default `null #[]), (Lean.Syntax.node default `null #[]), (Lean.Syntax.node default `Lean.Parser.Term.attrKind #[(Lean.Syntax.node default `null #[])]), (Lean.Syntax.atom default "syntax"), (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.precedence #[(Lean.Syntax.atom default ":"), (Lean.Syntax.node default `num #[(Lean.Syntax.atom default "1024")])])]), (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.Command.namedName #[(Lean.Syntax.atom default "("), (Lean.Syntax.atom default "name"), (Lean.Syntax.atom default ":="), mkIdent kindName, (Lean.Syntax.atom default ")")])]), (Lean.Syntax.node default `null #[]), (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.Syntax.cat #[(mkIdent `num), (Lean.Syntax.node default `null #[])])]), (Lean.Syntax.atom default ":"), cat])
  elabCommand numSyntaxDecl

  let pat ← liftTermElabM <| (q(1) : Expr).toPattern
  addExternalEquivalence kindName cat.getId kindName pat #[.node default `Lean.Parser.Syntax.cat #[(mkIdent `num), (Lean.Syntax.node default `null #[])]] checkInjective? checkSurjective? castFn

  let target : TSyntax `term := mkStrLit kindName.toString
  let attr ← `(attrInstance| $(mkIdent `external_elab):ident $(← mkIdentFromRef kindName):ident)
  let matcher_def : Syntax ← `(@[$attr]
      public aux_def elabRules $(mkIdent kindName) : ExternalElabSignature :=
      fun stx _ => pure ( ( ⟨($target).toName⟩ : ExternalEquivalenceKey), ([] : List (Name × Syntax)), ([] : List (Name × Syntax)) ))
  elabCommand matcher_def


  let kindName := externalScientificKind cat
  let scientificSyntaxDecl : TSyntax `command := .mk <| (Lean.Syntax.node default `Lean.Parser.Command.syntax #[(Lean.Syntax.node default `null #[]), (Lean.Syntax.node default `null #[]), (Lean.Syntax.node default `Lean.Parser.Term.attrKind #[(Lean.Syntax.node default `null #[])]), (Lean.Syntax.atom default "syntax"), (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.precedence #[(Lean.Syntax.atom default ":"), (Lean.Syntax.node default `num #[(Lean.Syntax.atom default "1024")])])]), (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.Command.namedName #[(Lean.Syntax.atom default "("), (Lean.Syntax.atom default "name"), (Lean.Syntax.atom default ":="), (mkIdent kindName), (Lean.Syntax.atom default ")")])]), (Lean.Syntax.node default `null #[]), (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.Syntax.cat #[(mkIdent `scientific), (Lean.Syntax.node default `null #[])])]), (Lean.Syntax.atom default ":"), cat])
  elabCommand scientificSyntaxDecl

  let pat ← liftTermElabM <| (q(1.0 : Real) : Expr).toPattern
  addExternalEquivalence kindName cat.getId kindName pat #[.node default `Lean.Parser.Syntax.cat #[(mkIdent `scientific), (Lean.Syntax.node default `null #[])]] checkInjective? checkSurjective? -- TODO: casting functions for scientific too (and make the interface a little nicer)

  let target : TSyntax `term := mkStrLit kindName.toString
  let attr ← `(attrInstance| $(mkIdent `external_elab):ident $(← mkIdentFromRef kindName):ident)
  let matcher_def : Syntax ← `(@[$attr]
      public aux_def elabRules $(mkIdent kindName) : ExternalElabSignature :=
      fun stx _ => pure ( ( ⟨($target).toName⟩ : ExternalEquivalenceKey), ([] : List (Name × Syntax)), ([] : List (Name × Syntax)) ))
  elabCommand matcher_def
