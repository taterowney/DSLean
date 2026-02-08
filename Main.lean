import DSLean

def main : IO UInt32 := do
  IO.println "DSLean loaded. Try: lake env lean DSLean/Demos.lean"
  pure 0
