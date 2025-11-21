import Lean
import Mathlib.FieldTheory.Finite.Basic
import Std.Internal.Parsec
import Std.Internal.Parsec.Basic
import Std.Internal.Parsec.String
import Qq.Macro
import ExternalComputationsInLean.Pattern
import Mathlib.Data.Finset.Insert
import ExternalComputationsInLean.Elaborator
import Lean.Elab.Command
import ExternalComputationsInLean.Pattern
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

import Canonical

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq
open Std.Internal.Parsec Std.Internal.Parsec.String
open Std.Internal

@[simp]
theorem conv1  {x : Real} {y : Int} (hy : y ≥ 0) : x^y = x^(Int.toNat y) := by
  sorry

-- macro "tac" : tactic => `(tactic| try decide; try simp_all <;> grind; try grind; try sorry)
macro "tac" : tactic => `(tactic| sorry)


declare_syntax_cat external
syntax "True" : external
syntax "False" : external
syntax external " /\\ " external : external
syntax external " \\/ " external : external
syntax "not " external : external
syntax external " -> " external : external
syntax "(" external ")" : external

syntax "let " ident (" : " external )? ":=" external " in " external : external
-- syntax "let " ident (" : " external)? ":=" external external " in " external : external -- Function application (jank)
syntax "(*" str "*)" external : external
syntax "fun " ident (" : " external)? " => " external : external
syntax:60 external:60 external:61 : external -- why not work :(
syntax "_" : external
syntax num : external
syntax ident : external
syntax "- " external : external

syntax "Gappa.Gappa_pred_bnd.Float1" external : external
syntax "Gappa.Gappa_definitions.Float2" : external
syntax "Gappa.Gappa_definitions.makepairF": external
syntax "Gappa.Gappa_definitions.BND" : external
syntax "Gappa.Gappa_pred_bnd.constant1" : external
syntax "Gappa.Gappa_tree.simplify " str : external
syntax "Reals.Rdefinitions.Rle" : external
syntax "Reals.R_sqrt.sqrt" : external
syntax "Reals.Rdefinitions.Rmult" : external
syntax "Gappa.Gappa_pred_bnd.sqrtG" : external
syntax "Gappa.Gappa_pred_bnd.mul_pp" : external
syntax "Gappa.Gappa_pred_bnd.add" : external
syntax "Gappa.Gappa_pred_bnd.div_pp" : external
syntax "Reals.Rdefinitions.Rplus" : external
syntax "Reals.Rdefinitions.Rdiv" : external
syntax "Reals.Rdefinitions.Rsub" : external
syntax "Reals.Rdefinitions.R" : external

structure ExternalParserContext where
  bvars : Array Name := #[]
instance : Inhabited ExternalParserContext :=
  ⟨{ bvars := {} }⟩

-- def mkReal (n : Expr) : MetaM Expr := do
--   let ofNat := mkApp (mkConst ``OfNat.ofNat [0]) (mkConst ``Real)
--   let n' := mkApp ofNat n
--   let inst ← synthInstance (mkApp (mkApp (mkConst ``OfNat [0]) (mkConst ``Real)) n)
--   return mkApp n' inst
  -- return n'

def mkReal (n : Expr) : MetaM Expr := do
  let ofInt := mkApp (mkConst ``Int.cast [0]) (mkConst ``Real)
  -- let n' := mkApp ofNat n
  -- let inst ← synthInstance (mkApp (mkConst ``IntCast [0]) (mkConst ``Real))
  let inst := q(Real.instIntCast)
  return mkApp2 ofInt inst n


def mkExponent (base : Expr) (exp : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp3 (mkConst ``HPow [0, 0, 0]) (mkConst ``Real []) (mkConst ``Int []) (mkConst ``Real []))
  return mkApp6 (mkConst ``HPow.hPow [0, 0, 0]) (mkConst ``Real []) (mkConst ``Int []) (mkConst ``Real []) inst base exp


def mkFloat (significand : Expr) (exponent : Expr) (base : Q(Real) := q(2)) : MetaM Expr := do
  let s' ← mkReal significand
  let e' ← mkExponent base exponent
  let inst ← synthInstance (mkApp3 (mkConst ``HMul [0, 0, 0]) (mkConst ``Real []) (mkConst ``Real []) (mkConst ``Real []))
  return mkApp6 (mkConst ``HMul.hMul [0, 0, 0]) (mkConst ``Real []) (mkConst ``Real []) (mkConst ``Real []) (inst) s' e'







def mkFloatPartial : MetaM Expr := do
  return q(fun s : Int => fun e : Int => (s : Real) * ((2:Real) ^ e))



def mkPredConstPartial (t : Expr) (type : Q(Prop)) : Expr :=
  -- mkApp q(fun (t : Prop) => fun (_ : Unit) => fun (i : Set Real) => fun (_ : Unit) => t) t
  mkApp q(fun (t : $type) => fun (_ : Unit) => t) t


def automation_hammer3 : TermElabM Expr :=do
    let tac_stx : TSyntax `term ← `(term| by tac)
    let tac ← Term.elabTerm tac_stx none
    return Expr.lam `_ (mkConst ``Unit [])
        (Expr.lam `_ q(Set Real)
          (Expr.lam `_ (mkConst ``Unit [])
            tac BinderInfo.default
          )
          BinderInfo.default
        )
        BinderInfo.default

def automation_hammer5 : TermElabM Expr :=do
    let tac_stx : TSyntax `term ← `(term| by tac)
    let tac ← Term.elabTerm tac_stx none
    return Expr.lam `_ (← mkFreshTypeMVar)
        (Expr.lam `_ (← mkFreshTypeMVar)
          (Expr.lam `_ (← mkFreshTypeMVar)
            (Expr.lam `_ (← mkFreshTypeMVar)
              (Expr.lam `_ (← mkFreshTypeMVar)
                tac BinderInfo.default
              )
              BinderInfo.default
            )
            BinderInfo.default
          )
        BinderInfo.default
        ) BinderInfo.default

def automation_hammer8 : TermElabM Expr :=do
    let tac_stx : TSyntax `term ← `(term| by tac)
    let tac ← Term.elabTerm tac_stx none
    return Expr.lam `_ (← mkFreshTypeMVar)
        (Expr.lam `_ (← mkFreshTypeMVar)
          (Expr.lam `_ (← mkFreshTypeMVar)
            (Expr.lam `_ (← mkFreshTypeMVar)
              (Expr.lam `_ (← mkFreshTypeMVar)
                (Expr.lam `_ (← mkFreshTypeMVar)
                  (Expr.lam `_ (← mkFreshTypeMVar)
                    (Expr.lam `_ (← mkFreshTypeMVar)
                      tac BinderInfo.default
                    )
                    BinderInfo.default
                  )
                  BinderInfo.default
                )
                BinderInfo.default
              )
              BinderInfo.default
            )
          BinderInfo.default
        )
        BinderInfo.default
        )
      BinderInfo.default

set_option pp.rawOnError true
partial def elabDSL (stx : Syntax) (c : ExternalParserContext := default) : TermElabM Expr := do
  match stx with
  | `(external| $fn:external $arg:external) => do
    let fn' ← elabDSL fn c
    let arg' ← elabDSL arg c
    -- logInfo m!"Function application: {fn'} applied to {arg'.dbgToString}"
    return mkApp fn' arg'
  | `(external| True) => return q(«True»)
  | `(external| False) => return q(«False»)
  | `(external| $x /\ $y) => do
    let x' ← elabDSL x c
    let y' ← elabDSL y c
    return .app ( .app ( .const ``And []) x') y'
  | `(external| $x \/ $y) => do
    let x' ← elabDSL x c
    let y' ← elabDSL y c
    return .app ( .app ( .const ``Or []) x') y'
  | `(external| not $x) => do
    let x' ← elabDSL x c
    return .app ( .const ``Not []) x'
  | `(external| $x -> $y) => do
    let x' ← elabDSL x c

    let x_identifier := x.raw.prettyPrint |>.pretty
    let c' := { c with bvars := #[x_identifier.toName] ++ c.bvars }
    let y' ← elabDSL y c'
    return mkForall `_ BinderInfo.default x' y'
  | `(external| ( $x ) ) => elabDSL x c
  | `(external| let $id:ident $[ : $ty:external]? := $val:external in $body:external) => do
    let ty' ← match ty with
      | some tyStx => elabDSL tyStx c
      | none => mkFreshTypeMVar

    let val' ← elabDSL val c
    let idName := id.getId
    let c' := { c with bvars := #[idName] ++ c.bvars } -- TODO: kinda jank... depends on how Lean automatically assigns de Bruijn indices
    -- Rn this works badly if a variable is shadowed/redeclared
    let body' ← elabDSL body c'
    let out := Expr.letE idName ty' val' body' (nondep := «false»)
    return out
  | `(external| fun $id:ident $[ : $ty:external]? => $body:external) => do
    let binder_type ← mkFreshTypeMVar

    let idName := id.getId
    let c' := { c with bvars := #[idName] ++ c.bvars }
    let body' ← elabDSL body c'

    let out := Expr.lam idName binder_type body' BinderInfo.default
    return out
  | `(external| (* $_:str *) $rest:external) => elabDSL rest c

  | `(external| Gappa.Gappa_pred_bnd.Float1 $r:external) => do
    let r' ← elabDSL r c
    mkReal r'
  | `(external| Gappa.Gappa_definitions.Float2) => do
    mkFloatPartial

  | `(external| Gappa.Gappa_definitions.makepairF) => do
    return q(fun f1 : Real => fun f2 : Real => Set.Icc f1 f2)
  | `(external| Gappa.Gappa_definitions.BND) => do
    return q(fun r : Real => fun i : Set Real => r ∈ i)
  | `(external| Reals.Rdefinitions.Rle) => do
    return q(fun x : Real => fun y : Real => x ≤ y)
  | `(external| Reals.R_sqrt.sqrt) => do
    return q(fun (x : Real) => Real.sqrt x)
  | `(external| Reals.Rdefinitions.Rmult) => do
    return q(fun (x : Real) => fun (y : Real) => x * y)
  | `(external| Reals.Rdefinitions.Rplus) => do
    return q(fun (x : Real) => fun (y : Real) => x + y)
  | `(external| Reals.Rdefinitions.Rdiv) => do
    return q(fun (x : Real) => fun (y : Real) => x / y)
  | `(external| Reals.Rdefinitions.Rsub) => do
    return q(fun (x : Real) => fun (y : Real) => x - y)
  | `(external| Reals.Rdefinitions.R) => do
    return q(Real)

  | `(external| Gappa.Gappa_pred_bnd.constant1) => do
      automation_hammer3
  | `(external| Gappa.Gappa_pred_bnd.sqrtG) => do
      automation_hammer5
  | `(external| Gappa.Gappa_pred_bnd.mul_pp) => do
      automation_hammer8
  | `(external | Gappa.Gappa_pred_bnd.add) => do
      automation_hammer8
  | `(external | Gappa.Gappa_pred_bnd.div_pp) => do
      automation_hammer8

  | `(external| Gappa.Gappa_tree.simplify $_) => do
    -- let tac_stx : TSyntax `term ← `(term| by tac)
    let tac_stx : TSyntax `term ← `(term| by sorry)

    let rest' ← Term.elabTerm tac_stx none
    return rest'

  | `(external | _) => do
    -- return .mvar (← mkFreshMVarId)
    return q(())

  -- | `(num | $n:num) => do
  --   let litVal := n.getNat
  --   return mkNatLit litVal -- TODO: why this not work :(
  | `(ident| $id) => do
    let n := id.raw.prettyPrint |>.pretty
    if let some val := String.toInt? n then
      return mkIntLit val

    match c.bvars.idxOf? n.toName with
    | some idx => return mkBVar idx
    | none => throwError "unknown identifier {n} ({id}) (available: {c.bvars})"
  -- | _ => throwError "not implemented"



partial def preprocess (s : String) : IO String :=
  -- let escaped_comments := s.replace "(*" "(*\"" |>.replace "*)" "\"*)"
  let escaped_comments := s.replace "(*" "/-" |>.replace "*)" "-/"
  let rec loop (input : String) (acc : String := "") : String :=
    if input = "" then acc else
    if input.dropWhile (· == ' ') |>.startsWith "Gappa.Gappa_tree.simplify" then
      loop (input.dropWhile (· != '\n') |>.drop 1) (acc ++ "Gappa.Gappa_tree.simplify \"_\" in ")
    else
      let line := input.takeWhile (· != '\n')
      loop (input.dropWhile (· != '\n') |>.drop 1) (acc ++ line ++ "\n")
  let escaped := loop escaped_comments
  IO.Process.run {
    cmd := "python3",
    args := #[s!"/Users/trowney/Desktop/Code/gappa/gappa/preprocess.py", escaped],
    stdin := .piped,
    stdout := .piped,
    stderr := .piped
  }





def testParse (input : String) : TermElabM Expr := do
  let p := Parser.categoryParser `external 1 |>.fn
  let e ← getEnv
  let ctx := Parser.mkInputContext input "<input>"
  let out := p.run ctx {env := e, options := default} (Parser.getTokenTable e) {cache := Parser.initCacheForInput input, pos := 0}

  -- logInfo m!"Errors: {out.errorMsg}"
  -- logInfo m!"Parsed: {out.stxStack.back}"

  elabDSL out.stxStack.back

-- #eval testParse test_input2
-- syntax (name := parse_external_cmd) "#parse_external " term : command

-- @[command_elab parse_external_cmd]
-- def elabParseExternal : CommandElab := fun stx => do
--   liftTermElabM do
--     let s ← elabTerm stx[1] (some q(String))

--     -- logInfo m!"Elaborated to: {← quote_expr s}"
--     let Expr.lit (.strVal input) := s | throwError "expected string literal"
--     -- let input := "let f1 := false in true"
--     let expr ← testParse input
--     let expr ← instantiateMVars expr
--     Meta.check expr
--     logInfo m!"{expr} : {← inferType expr}"
--     logInfo m!"Quoted: {← quote_expr expr}"

syntax (name := parse_external_cmd) "parse_external " term : term

@[term_elab parse_external_cmd]
def elabParseExternal : TermElab := fun stx type? => do
  let s ← elabTerm stx[1] (some q(String))

  let Expr.lit (.strVal input) := s | throwError "expected string literal"
  let input ← preprocess input
  logInfo m!"Preprocessed input: {input}"
  let expr ← testParse input
  let expr ← instantiateMVars expr
  Meta.check expr
  logInfo m!"{expr} : {← inferType expr}"
  -- logInfo m!"Quoted: {← quote_expr expr}"
  return expr




/-
Bucket list for actual parser:
- Custom parse functions for numerals, etc.
- Can deal with function application without crashing out (curry stuff that has arguments automatically)
- No janky preprocessing for comments
- Doesn't keep environment from file where syntax category is instantiated
- Can put tactics easily
- Handles bvars under the hood
- Stringifier opens functions that are not known to see if they can be translated by their contents
-/


-- example (h1 : 3 ∉ Set.Icc (3 * 2 ^ 0) (3 * 2 ^ 0)) (h : ¬(3:Real) * 2 ^ (0:Int) ≤ 3) : «False»:= by
--   try simp_all only [zpow_zero, mul_one, le_refl, not_true_eq_false] <;> grind
--   try grind
