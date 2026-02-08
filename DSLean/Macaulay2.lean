import Lean

private def getEnvOrDefault (name defaultValue : String) : IO String := do
  match (← IO.getEnv name) with
  | some value =>
      if value.isEmpty then
        pure defaultValue
      else
        pure value
  | none => pure defaultValue

private def getMacaulay2Path : IO String :=
  getEnvOrDefault "DSLEAN_M2_BIN" "/usr/bin/M2"

/-- Run a Macaulay2 script and return stdout. -/
def runMacaulay2 (script : String) : IO String := do
  let m2Path ← getMacaulay2Path
  IO.Process.run {
    cmd := m2Path
    args := #["--silent", "--no-readline", "-e", script]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }

/-- Example: compute a Groebner basis for a small ideal. -/
def macaulay2GroebnerDemo : IO String :=
  runMacaulay2 "R=QQ[x,y]; I=ideal(x^2-y,y^2-x); << toString gb I << endl;"

/-- Example: eliminate `y` from a polynomial ideal. -/
def macaulay2EliminationDemo : IO String :=
  runMacaulay2 "R=QQ[x,y]; I=ideal(y-x^2,y-1); J=eliminate(y,I); << toString gens J << endl;"
