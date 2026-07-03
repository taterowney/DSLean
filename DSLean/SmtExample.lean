import DSLean.Command
import Mathlib.Tactic


open Lean Meta Elab Term Qq

/-- Not declared natively in Lean (it only has the natural number version for left shift) -/
def BitVec.shiftLeft' (bv : BitVec n) (amt : BitVec n) : BitVec n := BitVec.shiftLeft bv (BitVec.toNat amt)


external to_smtlib where
  "(declare-const" $name "(_" "BitVec" n ")" ")\n" rest <== ∃ (name : BitVec n), rest

  "(=" a b ")" <== a = b

  "(or" a b ")" <== a ∨ b
  "(and" a b ")" <== a ∧ b
  "(not" a ")" <== ¬ a

  "(bvadd" a b ")" <== BitVec.add a b
  "(bvsub" a b ")" <== BitVec.sub a b
  "(bvmul" a b ")" <== BitVec.mul a b
  "(bvudiv" a b ")" <== BitVec.udiv a b
  "(bvand" a b ")" <== BitVec.and a b
  "(bvor" a b ")" <== BitVec.or a b
  "(bvnot" a ")" <== BitVec.not a
  "(bvshl" bv amt ")" <== BitVec.shiftLeft' bv amt
  "(bvashr" bv amt ")" <== BitVec.sshiftRight' bv amt -- Lean identifier has an extra `s` for reasons unknown

  "(bvule" a b ")" <== BitVec.ule a b
  "(bvult" a b ")" <== BitVec.ult a b

  "true" <== true -- Reasonable to assume that boolean and propositional versions can be treated the same, since SMT-LIB makes no distinction
  "false" <== false
  "true" <== True
  "false" <== False



def to_smtlib (problem : Expr) : TermElabM String := do
  let all := (← toExternal' `to_smtlib problem).replace "\\n" "\n"

  let declarations := all.splitOn "\n" |>.takeWhile (fun s => s.trimAscii.startsWith "(declare")
  let asserts := all.splitOn "\n" |>.getLast?.getD ""

  return s!"(set-logic QF_BV)\n(set-option :produce-models true)\n{String.intercalate "\n" declarations}\n(assert {asserts})\n(check-sat)\n(get-model)\n(exit)"




/-
Examples
-/

#eval do
  logInfo (← to_smtlib q(

    -- Reflexivity (SAT)
    ∃ (x : «BitVec» 8), x.ule x

  ))

  logInfo (← to_smtlib q(

    -- Left-shift and right-shift are *not* inverses (SAT)
    ∃ (x : «BitVec» 8) (y : «BitVec» 8), (x.sshiftRight' y).shiftLeft' y ≠ x

  ))

  logInfo (← to_smtlib q(

    -- Adding and bitwise-OR are the same for a number and its bitwise negation (UNSAT)
    ∃ (x : «BitVec» 8), x.add (x.not) ≠ x.or (x.not)

  ))
