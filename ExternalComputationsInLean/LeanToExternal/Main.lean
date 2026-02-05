import Lean
import Std.Internal.Parsec
import Std.Internal.Parsec.Basic
import Std.Internal.Parsec.String
import Qq.Macro
import Lean.Elab.Command
import ExternalComputationsInLean.Utils.Pattern
import Lean.Parser.Command
import Lean.Parser.Syntax
import Lean.Parser.Term
import Lean.Meta

import ExternalComputationsInLean.LeanToExternal.Parsing
import ExternalComputationsInLean.LeanToExternal.Elaboration

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq
open Std.Internal.Parsec Std.Internal.Parsec.String
open Std.Internal Parser Command Syntax Quote



/-- Set up an external parser category for a DSL with this name, and add some default elaborators that are a part of every DSL. -/
def initializeExternalCategory (cat : TSyntax `ident) (checkInjective? : Bool) (checkSujective? : Bool) (castFn : Expr) : CommandElabM Unit := do
  elabCommand (← `(declare_syntax_cat $cat))

  declareDefaultElaborators cat checkInjective? checkSujective? castFn



/-- Set up parsing/elaboration rules for a specific external syntax pattern. -/
def declareExternal (cat : Name) (patterns : Array (TSyntax `stx)) (target : TSyntax `term) (checkInjective? : Bool) (checkSujective? : Bool) (options : ExternalEquivalenceOptions) : CommandElabM Unit := do
  let ⟨k, variableNames, binderNames⟩ ← declareExternalSyntax cat patterns options -- Look through the external pattern, gather all the necessary variables, and declare a syntax node that parses that pattern

  let targetPat ← liftTermElabM <| target.toPattern none variableNames.toArray binderNames.toArray checkInjective? checkSujective? -- Make an ExprPattern from the target expression. This checks to make sure the variable names line up with those in the syntax patterns.
  -- logInfo m!"Declared external equivalence: {targetPat.expr.expr}"

  addExternalEquivalence k cat k targetPat patterns checkInjective? checkSujective? -- Add information about this equivalence to the environment

  declareExternalElaborator k cat patterns ⟨k⟩ -- Declare an elaborator for this external syntax


/-- Parse an input string according to the external syntax category `cat`, returning the corresponding `Syntax` object. Additionally makes sure there's no extra stuff hanging out at the end. TODO: ascii character byte vs character length (`runParserCategory`) -/
def parseExternal (cat : Name) (input : String) : TermElabM Syntax := do
  let p := Parser.categoryParser cat 0 |>.fn -- Process the syntax with our custom parser
  let e ← getEnv
  let ctx := Parser.mkInputContext input "<input>"
  let out := p.run ctx {env := e, options := default} (Parser.getTokenTable e) {cache := Parser.initCacheForInput input, pos := 0} -- TokenTable here might allow for non-unicode characters
  if out.hasError then
    throwError m!"Syntax error in input: {out.errorMsg}"
  if out.pos.byteIdx != input.length then
    throwError m!"Syntax error in input: unexpected trailing characters {input.drop out.pos.byteIdx}"
  return out.stxStack.back


/-- Try to synthesize and assign every typeclass metavariable occurring in `e`. Have to do this manually, since unsynthesized typeclasses aren't recorded in `pendingMVars` for some reason (likely because of the various stages of abstraction and other tomfoolery) -/
partial def synthTCMVarsIn (e : Expr) : MetaM Expr := do
  let mvars ← Meta.getMVars e
  for mvarId in mvars do
    if !(← mvarId.isAssigned) then
      mvarId.withContext do
        let decl ← mvarId.getDecl
        if (← Meta.isClass? decl.type).isSome then
          let inst ← Meta.synthInstance decl.type
          mvarId.assign inst
  instantiateMVars e


/-- Elaborate a set of parsed external syntax, recursively filling in blanks. TODO: `elabContinuation` currently pretty simplistic: might want to add type filtration (requires delaboration/backtracking?), interface with state, and maybe make it a parameter -/
partial def elabExternal (cat : Name) (input : Syntax) (expectedType? : Option Expr := none) : TermElabM Expr := do
  if input.getKind == (externalNumKind (mkIdent cat)) then -- Hack: `num`s are processed separately since atoms don't play nice with numbers, so just manually translate them to `Nat`s
    match input.getArg 0 with
    | .node _ `num contents =>
      match contents.toList with
      | .atom _ val :: _ =>
        match val.toNat? with
        | some n =>
          let some e ← liftCommandElabM <| getExternalEquivalence ⟨externalNumKind (mkIdent cat)⟩ | throwError m!"Internal assertion failed: no external equivalence found for key '{externalNumKind (mkIdent cat)}'"
          let some castFn := e.postprocess | throwError m!"Internal assertion failed: no cast function found for num syntax"
          return mkApp castFn (mkNatLit n)
        | _ => throwError m!"Internal assertion failed: malformed num syntax"
      | _ => throwError m!"Internal assertion failed: malformed num syntax"
    | _ => throwError m!"Internal assertion failed: malformed num syntax"

  if input.getKind == (externalScientificKind (mkIdent cat)) then -- Hack: `scientific` numbers are processed separately since atoms don't play nice with numbers, so just manually translate them to `Real`s
    match input.getArg 0 with
    | .node _ `scientific contents =>
      match contents.toList with
      | .atom _ val :: _ =>
        throwError "TODO: scientific syntax elaboration"
        -- match val.toFloat? with
        -- | some f =>
        --   let some e ← liftCommandElabM <| getExternalEquivalence ⟨externalScientificKind (mkIdent cat)⟩ | throwError m!"Internal assertion failed: no external equivalence found for key '{externalScientificKind (mkIdent cat)}'"
        --   let some castFn := e.postprocess | throwError m!"Internal assertion failed: no cast function found for scientific syntax"
        --   return mkApp castFn (mkFloatLit f)
        -- | _ => throwError m!"Internal assertion failed: malformed scientific syntax"
      | _ => throwError m!"Internal assertion failed: malformed scientific syntax"
    | _ => throwError m!"Internal assertion failed: malformed scientific syntax"

  match externalElabAttribute.getEntries (← getEnv) input.getKind with
  | [] => throwError m!"Internal assertion failed: no elaborator found for external syntax of kind '{input.getKind}'"
  | elab_fn :: _ =>
    let (key, blankContents, binderContents) ← elab_fn.value input none
    let some e ← liftCommandElabM <| getExternalEquivalence key | throwError m!"Internal assertion failed: no external equivalence found for key '{key.name}'"

    unless e.isSurjective do
      throwError m!"Elaboration failed: external equivalence for syntax kind '{input.getKind}' is not surjective, cannot elaborate from external syntax to Lean expression"

    if !e.exprPattern.getVars.toList.isPerm (blankContents.map Prod.fst) then
      throwError m!"Internal assertion failed: variable names in external equivalence do not match provided values"

    let binderNames ← binderContents.mapM (fun ⟨n, stx⟩ => do
      match stx with
      | Lean.Syntax.ident _ name _ _ => return (n, name.toName)
      | _ => throwError m!"Internal assertion failed: binder syntax is not an identifier")
    if !e.exprPattern.getBinderVars.toList.isPerm (binderNames.map Prod.fst) then
      throwError m!"Internal assertion failed: binder names in external equivalence do not match provided binders"

    let binderNameCont := fun (n : Name) => match binderNames.find? (fun (bn, _) => bn == n) with
      | some (_, name) => return name
      | none => throwError m!"Unification failed: no value provided for binder blank '{n}'"
    let out ← instantiateMVars (← e.exprPattern.unify expectedType? (blankCont blankContents) binderNameCont)
    synthTCMVarsIn out

where blankCont (blankContents : List (Name × Syntax)) (name : Name) (expectedType? : Option Expr) : TermElabM Expr := do
  match blankContents.find? (fun (n, _) => n == name) with
  | some (_, stx) => elabExternal cat stx expectedType?
  | none => throwError m!"Unification failed: no value provided for blank '{name}'"


/-- Process (parse and elaborate) an input string according to the external syntax category `cat`. -/
def processExternal (cat : Name) (input : String) : TermElabM Expr := do
  let stx ← parseExternal cat input
  elabExternal cat stx
