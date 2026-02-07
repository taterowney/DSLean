import Lean
import Std.Internal.Parsec
import Std.Internal.Parsec.Basic
import Std.Internal.Parsec.String
import Qq.Macro
import Lean.Elab.Command
import DSLean.Utils.Pattern
import Lean.Parser.Command
import Lean.Parser.Syntax
import Lean.Parser.Term

import DSLean.ExternalToLean.Basic
import DSLean.Utils.Syntax


open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq
open Std.Internal.Parsec Std.Internal.Parsec.String
open Std.Internal Parser Command Syntax Quote
open Lean.Elab.Command

/-- By default, we try to make everything as left-associative as possible, so defining things like function application doesn't interfere with other syntax that has two `Syntax.cat`s in a row. -/
def addPrecedences (syntaxPatterns : Array Syntax) (options : ExternalEquivalenceOptions) : (Array Syntax) :=
  let startsWithAtom := match syntaxPatterns[0]? with
    | some (.node _ `Lean.Parser.Syntax.atom _) => true
    | _ => false

  let hasSeparators := syntaxPatterns.size > 1 && syntaxPatterns[1:].any fun p =>
    match p with
    | .node _ `Lean.Parser.Syntax.atom _ => true
    | _ => false

  syntaxPatterns.zipIdx.map fun (p, i) =>
    match p with
    | .node info k args =>
      match k with
      | `Lean.Parser.Syntax.cat =>
        let catDecl := args[0]?.getD (mkIdent .anonymous |>.raw)
        if [.anonymous, `ident, `num, `str].contains catDecl.getId then -- Don't add precedences to things that don't like them
          p
        else
          let prec := if startsWithAtom && hasSeparators then (60:Int) else -- If it's nicely interspersed with atoms, just keep the precedences normal
            if !options.rightAssociative then -- If it's weird and (by default) left associative, then assign everything except the first to higher precedence, so that leading `Syntax.cat`s don't screw up other patterns
              if i == 0 then 60 else 61
            else
              if i == 0 then 61 else 60 -- If right associative, make it heterogenous the other way around
          -- let prec := prec + options.precedence
          let newArgs := args.push
            (Lean.Syntax.node default `null #[(Lean.Syntax.node default `Lean.Parser.precedence #[(Lean.Syntax.atom default ":"), (Lean.Syntax.node default `num #[(Lean.Syntax.atom default prec.toNat.repr)])])]) -- Add a precedence annotation to the end of the syntax pattern
          .node info k newArgs
      | _ => p
    | x => x


/-- From Lean/Elab/Syntax.lean -/
private partial def mkNameFromParserSyntax (catName : Name) (stx : Syntax) : MacroM Name := do
  mkUnusedBaseName <| Name.mkSimple <| appendCatName <| visit stx ""
where
  visit (stx : Syntax) (acc : String) : String :=
    match stx.isStrLit? with
    | some val => acc ++ (val.trimAscii.copy.map fun c => if c.isWhitespace then '_' else c).capitalize
    | none =>
      match stx with
      | Syntax.node _ k args =>
        if k == ``Lean.Parser.Syntax.cat then
          acc ++ "_"
        else if k == ``Lean.Parser.Syntax.unicodeAtom && args.size > 1 then
          -- in `unicode(" ≥ ", " >= ")` only visit `" ≥ "`.
          visit args[1]! acc
        else
          args.foldl (init := acc) fun acc arg => visit arg acc
      | Syntax.ident ..    => acc
      | Lean.Syntax.atom ..     => acc
      | Syntax.missing     => acc

  appendCatName (str : String) :=
    match catName with
    | .str _ s => s ++ str
    | _ => str

/--
Add macro scope to `name` if it does not already have them, and `attrKind` is `local`. From Lean/Elab/Syntax.lean
-/
private def addMacroScopeIfLocal [MonadQuotation m] [Monad m] (name : Name) (attrKind : Syntax) : m Name := do
  if isLocalAttrKind attrKind && !name.hasMacroScopes then
    MonadQuotation.addMacroScope name
  else
    return name



/-- Creates a custom syntax declaration based on the patterns given; identifiers are assumed to refer to bound variable names not syntax categories. Lots borrowed from `elabSyntax` function in `Lean.Elab.Syntax` -/
def declareExternalSyntax (cat : Name) (patterns : Array Syntax) (options : ExternalEquivalenceOptions) : CommandElabM (SyntaxNodeKind × List Name × List Name) := do
  let mut syntaxParts : Array Syntax := #[]
  let mut variableNames : List Name := []
  let mut binderNames : List Name := []
  for p in patterns do
    match p with
    | .node _ k args =>
      match k with
      | `Lean.Parser.Syntax.atom =>
        syntaxParts := syntaxParts.push p
      | `Lean.Parser.Syntax.cat =>
        match args.toList with
        | (.ident _ raw _ _ ) :: _ =>
          syntaxParts := syntaxParts.push (mkNode `Lean.Parser.Syntax.cat #[mkIdent cat])
          variableNames := (raw.toName) :: variableNames
        | _ => throwError m!"Unsupported cat args: {args}"
      | `stx.pseudo.antiquot =>
        match args.toList with
        | _ :: _ :: (.ident _ raw _ _ ) :: _ =>
          syntaxParts := syntaxParts.push (mkNode `Lean.Parser.Syntax.cat #[mkIdent `ident])
          binderNames := (raw.toName) :: binderNames
        | _ => throwError m!"Unsupported antiquot args: {args}"
      | _ => throwError m!"Unsupported syntax node kind: {k}"
    | x => throwError m!"Unsupported syntax part: {x}"


  syntaxParts := addPrecedences syntaxParts options
  let syntaxParser := mkNullNode syntaxParts
  let (val, lhsPrec?) ← runTermElabM fun _ => Term.toParserDescr syntaxParser cat

  let prio := 0
  let prec := 60 + options.precedence


  let name ← addMacroScopeIfLocal (← liftMacroM <| mkNameFromParserSyntax cat syntaxParser) default
  let idRef := mkIdentFrom (mkNullNode patterns) (cat.appendAfter "ParserDescr") (canonical := true)
  let stxNodeKind := (← getCurrNamespace) ++ name
  let catParserId := mkIdentFrom idRef (cat.appendAfter "_parser") (canonical := true)
  let declName := mkIdentFrom idRef name (canonical := true)

  let attrInstance ← `(Term.attrInstance| $catParserId:ident $(quote prio):num)
  let attrInstances : TSepArray `Lean.Parser.Term.attrInstance "," := { elemsAndSeps := #[] }
  let attrInstances := attrInstances.push attrInstance


  let d ← if let some lhsPrec := lhsPrec? then
    `(@[$attrInstances,*] meta def $declName:ident : Lean.TrailingParserDescr :=
        ParserDescr.trailingNode $(quote stxNodeKind) $(quote prec.toNat) $(quote lhsPrec) $val)
  else
    let prec := 1024
    `(@[$attrInstances,*] meta def $declName:ident : Lean.ParserDescr :=
        ParserDescr.node $(quote stxNodeKind) $(quote prec) $val)

  elabCommand d
  return (stxNodeKind, variableNames, binderNames)
