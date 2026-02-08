import DSLean.Command
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
set_option linter.unusedVariables false set_option linter.unusedTactic false set_option linter.unreachableTactic false

open Lean Meta Elab Term Command Tactic

external Gappa_input where
  "(" x "+" y ")" <== x + y
  "(" x "-" y ")" <== x - y
  "(" x "*" y ")" <== x * y
  "(" x "/" y ")" <== x / y
  "sqrt(" x ")" <== Real.sqrt x
  "-" x <== - (x:Real)

  "(" x "->" y ")" <== x → y
  "(" x "/\\" y ")" <== x ∧ y
  "(" x "\\/" y ")" <== x ∨ y
  "not" x <== ¬ x

  "[" x "," y "]" <== Set.Icc x y
  x "in" y <== x ∈ y
  x "=" y <== x = y

/- Gappa's Coq output uses quite a few automation tactics that don't have direct equivalents in Lean, so we recreate them here. -/

/-- Automatically unfolds all local let/have declarations -/
elab "unfold_local" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let localDecls ← (← getLCtx).getFVarIds.filterMapM (fun id => do
      if ← id.isLetVar then
        let name := (mkIdent (← id.getUserName))
        return some (← `(Lean.Parser.Tactic.simpLemma| $name:term))
      else return none )
    Lean.Elab.Tactic.evalTactic <| ← `(tactic| dsimp [$localDecls,*] at *)
macro "tac" : tactic => `(tactic| sorry)

macro "constantBound" : tactic => `(tactic| unfold_local <;> norm_num <;> constructor <;> simp_all)
macro "sqrtG" : tactic => `(tactic| unfold_local <;> norm_num <;>
  constructor <;> apply (sq_le_sq₀ (by norm_num) (by norm_num)).mp
    <;> rw [Real.sq_sqrt (x := 2) (by norm_num)]
    <;> norm_num)
macro "mul_pp" : tactic => `(tactic| unfold_local <;> norm_num at * <;>
  constructor <;> apply (sq_le_sq₀ (by norm_num) (by norm_num)).mp
  <;> simp only [mul_pow, Real.sq_sqrt (x := 2) (by norm_num)]
  <;> norm_num)

external Gappa_output (numberCast := Int.ofNat) where
  x "->" y   ==> x → y; +rightAssociative
  x "/\\" y  ==> x ∧ y
  x "\\/" y  ==> x ∨ y
  "not" x    ==> ¬ x
  "True"     ==> True
  "False"    ==> False
  "(" inside ")"                      ==> inside
  "let" $n ":=" val "in" rest         ==> let n := val; rest
  "let" $n ":" ty ":=" val "in" rest  ==> let n:ty := val; rest
  "fun" $n "=>" rest                  ==> fun n => rest
  "fun" "(" $n ":" ty ")" "=>" body   ==> fun n:ty => body
  "-" x  ==> - x
  "_"    ==> _
  x y ==> (id ∘ x) y

  "Reals.Rdefinitions.R"                    ==> ℝ
  "Gappa.Gappa_pred_bnd.Float1" x           ==> (IntCast.intCast x : Real)
  "Gappa.Gappa_definitions.Float2" x y      ==> (IntCast.intCast x : Real) * ((2:Real) ^ (y:Int))
  "Gappa.Gappa_definitions.makepairF" x y   ==> Set.Icc x y
  "Gappa.Gappa_definitions.BND" x y         ==> x ∈ y
  "Gappa.Gappa_definitions.ABS" x y         ==> (abs x) ∈ y
  "Reals.Rdefinitions.Rle" x y              ==> x ≤ y
  "Reals.Rdefinitions.Rplus" x y            ==> x + y
  "Reals.Rdefinitions.Rminus" x y           ==> x - y
  "Reals.Rdefinitions.Rmult" x y            ==> x * y
  "Reals.Rdefinitions.Rdiv" x y             ==> x / y
  "Reals.Rdefinitions.Ropp" x               ==> - (x:Real)
  "Reals.R_sqrt.sqrt" x                     ==> Real.sqrt x

  "Gappa.Gappa_pred_bnd.constant1" a b c          ==> by constantBound <;> sorry
  "Gappa.Gappa_tree.simplify" a                   ==> by tac
  "Gappa.Gappa_pred_bnd.sqrtG" a b c d e          ==> by tac
  "Gappa.Gappa_pred_bnd.neg" a b c d e            ==> by constantBound <;> sorry
  "Gappa.Gappa_pred_bnd.add" a b c d e f g h      ==> by constantBound <;> sorry
  "Gappa.Gappa_pred_bnd.sub" a b c d e f g h      ==> by constantBound <;> sorry
  "Gappa.Gappa_pred_bnd.mul_pp" a b c d e f g h   ==> by tac
  "Gappa.Gappa_pred_bnd.div_pp" a b c d e f g h   ==> by tac
  "Gappa.Gappa_pred_abs.abs_of_bnd_p" a b c d e   ==> by tac
  "Gappa.Gappa_pred_bnd.square" a b c d e         ==> by tac
  "Gappa.Gappa_pred_bnd.subset" a b c d e         ==> by tac
  "Gappa.Gappa_rewriting.add_xilu" a b c d          ==> by tac
  "Gappa.Gappa_pred_bnd.intersect_hb" a b c d e f g ==> by tac
  "Gappa.Gappa_pred_bnd.intersect_bh" a b c d e f g ==> by tac
  "Gappa.Gappa_pred_bnd.union" a b c d              ==> by tac
  "Gappa.Gappa_rewriting.val_xabs" a b c d ==> by tac

  "proj1" x  ==> And.left x
  "proj2" x  ==> And.right x


/-- Tiny bit of auxiliary parsing to keep Gappa's output cleaner -/
declare_syntax_cat clean_gappa (behavior := symbol)
syntax "let" ident ("(" ident ":" ident ")")* ":" ident ":=" : clean_gappa
syntax "fun" (ident)* "=>" : clean_gappa
syntax "fun" ("(" ident ":" ident ")")* "=>" : clean_gappa

def Lean.TSyntax.str (s : TSyntax α) : String := (toString s).drop 1 |>.toString
def clean_gappa_macro (s : String) : TermElabM String := do
  try
    let pref := if s.trimAscii.startsWith "(" then "(" else ""
    let parsed ← parseExternal `clean_gappa (s.trimAscii.dropWhile '(').toString
    match parsed with
    | `(clean_gappa| let $bname:ident $[( $names:ident : $typs:ident)]* : $result:ident := ) =>
      return s!"{pref}let {bname.str} : {String.intercalate " -> " ((typs.map Lean.TSyntax.str).toList ++ [result.str])} := {String.intercalate " " (names.zip typs |>.map (fun (n, t) => s!"fun ({n.str} : {t.str}) =>") |>.toList)}"
    | `(clean_gappa| fun $names:ident* => ) =>
      return pref ++ String.intercalate " " (names.map (fun id => s!"fun {id.str} =>") |>.toList)
    | `(clean_gappa| fun $[( $names:ident : $typs:ident )]* => ) =>
      return pref ++ String.intercalate " " (names.zip typs |>.map (fun (n, t) => s!"fun ({n.str} : {t.str}) =>") |>.toList)
    | _ => return s
  catch _ => return s

/-- Make Gappa's output a little cleaner before translation, removing comments and super spam-y automation tactics to keep the final translation short -/
partial def preprocess (s : String) : TermElabM String := do
  let mut no_comments := s.foldl (fun (acc, inComment, prevIsStar) c =>
    if c == '*' && acc.back? == some '(' then (acc.dropEnd 1 |>.toString, true, true)
    else if inComment && c == ')' && prevIsStar then (acc, false, false)
    else if inComment then (acc, true, c == '*')
    else (acc ++ c.toString, false, false)
  ) ("", false, false) |>.1

  no_comments := no_comments.replace ":=" ":=\n" |>.replace "==>" "==>\n" |>.replace " in " " in\n" |>.replace "Gappa.Gappa_tree.simplify" "\nGappa.Gappa_tree.simplify" |>.replace "Reals.Rdefinitions.R" "Reals.Rdefinitions.R'" |>.replace "\n\n" "\n"
  let lines ← no_comments.splitOn "\n" |>.map (fun line => if line.trimAscii.startsWith "Gappa.Gappa_tree.simplify" && line.trimAscii.endsWith "in" then "Gappa.Gappa_tree.simplify _ in" else line) |>.mapM clean_gappa_macro
  return String.intercalate "\n" lines |>.replace "Reals.Rdefinitions.R'" "Reals.Rdefinitions.R"

/-- Solves interval arithmetic problems -/
elab "gappa" : tactic => do
  let goal ← getMainGoal
  let typ ← instantiateMVars (← goal.getType)
  let formatted ← toExternal `Gappa_input typ
  let res ← IO.FS.withTempFile fun handle path => do
    IO.FS.writeFile path s!"\{{formatted}}"
    IO.Process.run {
      cmd := (← IO.getEnv "DSLEAN_GAPPA_PATH").getD "gappa", args := #[s!"-Bcoq-lambda", path.toString],
      stdin := .piped, stdout := .piped, stderr := .piped
    }
  logInfo m!"Gappa raw: {res}"
  let input ← preprocess res
  logInfo m!"Gappa output: {input}"
  let proof ← fromExternal' `Gappa_output input

  let newhyp : Hypothesis := {
    userName := `h_gappa,
    type := ← Core.betaReduce (← Meta.whnf (← inferType proof)),
    value := ← Meta.whnf proof
  }
  let ⟨_, new⟩ ← goal.assertHypotheses #[newhyp]
  replaceMainGoal [new]

  Lean.Elab.Tactic.evalTactic (← `(tactic| norm_num at * ))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try grind ))
