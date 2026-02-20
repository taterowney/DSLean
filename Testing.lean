import Qq.Macro
open Lean Meta Qq Elab Command



private def addScope (isNewNamespace : Bool) (header : String) (newNamespace : Name)
    (isNoncomputable isPublic isMeta : Bool := false) (attrs : List (TSyntax ``Parser.Term.attrInstance) := []) :
    CommandElabM Unit := do
  modify fun s => { s with
    env    := s.env.registerNamespace newNamespace,
    scopes := { s.scopes.head! with
      header := header, currNamespace := newNamespace
      isNoncomputable := s.scopes.head!.isNoncomputable || isNoncomputable
      isPublic := s.scopes.head!.isPublic || isPublic
      isMeta := s.scopes.head!.isMeta || isMeta
      attrs := s.scopes.head!.attrs ++ attrs
    } :: s.scopes
  }
  pushScope
  if isNewNamespace then
    activateScoped newNamespace

private def addScopes (header : Name) (isNewNamespace : Bool) (isNoncomputable isPublic isMeta : Bool := false)
    (attrs : List (TSyntax ``Parser.Term.attrInstance) := []) : CommandElabM Unit :=
  go header
where go
  | .anonymous => pure ()
  | .str p header => do
    go p
    let currNamespace ← getCurrNamespace
    addScope isNewNamespace header (if isNewNamespace then Name.mkStr currNamespace header else currNamespace) isNoncomputable isPublic isMeta attrs
  | _ => throwError "invalid scope"

private def addNamespace (header : Name) : CommandElabM Unit :=
  addScopes (isNewNamespace := true) (isNoncomputable := false) (attrs := []) header

def withNamespace2 {α} (ns : Name) (elabFn : CommandElabM α) : CommandElabM α := do
  addNamespace ns
  let a ← elabFn
  logInfo m!"{ns.getNumParts}"
  modify fun s => { s with scopes := s.scopes.drop ns.getNumParts }
  pure a




#eval do
  addNamespace `test_ns
  withNamespace2 `test_ns do
    logInfo "hi"

-- namespace test_ns
-- end test_ns

namespace test_ns

-- @[scoped term_parser 0]
-- meta def translate_True2 : Lean.ParserDescr :=
--   ParserDescr.node `DSLean._internal.translate_PythonTrue 1024 (ParserDescr.symbol "True2")
scoped syntax "True" : term

end test_ns

-- #check True
