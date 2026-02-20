/- Various attributes and initializers used to keep track of external equivalences -/
import Lean
import DSLean.Utils.Pattern
open Lean Meta Elab Command

structure ExternalEquivalenceKey where
  name : Name
  deriving Inhabited, BEq, Hashable

/-- Keeps track of all information about an external equivalence. These are cached and can be retrieved using `getExternalEquivalence`. -/
structure ExternalEquivalence where
  syntaxCategory : Name
  stxNodeKind : SyntaxNodeKind
  exprPattern : ExprPattern
  rawSyntaxPatterns : Array Syntax
  isInjective : Bool
  isSurjective : Bool
  postprocess : Option Expr := none
  priority : Int := 0
deriving Inhabited


initialize externalEquivalenceCache : SimplePersistentEnvExtension (ExternalEquivalenceKey × ExternalEquivalence) (Std.HashMap ExternalEquivalenceKey ExternalEquivalence) ←
  registerSimplePersistentEnvExtension {
    name := `externalEquivalenceCache

    /- When a new entry is added, insert it into the map. -/
    addEntryFn := fun (st : Std.HashMap ExternalEquivalenceKey ExternalEquivalence) (k, v) =>
      st.insert k v

    /- When importing from other modules, merge the maps. -/
    addImportedFn := fun imports =>
      let flat := imports.flatten
      flat.foldl (fun acc m => acc.insert m.1 m.2) (Std.HashMap.emptyWithCapacity flat.size)
  }

/-- Adds a new external equivalence to the cache. -/
def addExternalEquivalence (name : Name) (syntaxCategory : Name) (stxNodeKind : SyntaxNodeKind) (exprPattern : ExprPattern) (rawSyntaxPatterns : Array Syntax) (isInjective : Bool) (isSurjective : Bool) (priority : Int := 0) (postprocess : Option Expr := none) : CommandElabM Unit := do
  let key : ExternalEquivalenceKey := { name }
  let value : ExternalEquivalence := { syntaxCategory, stxNodeKind, exprPattern, rawSyntaxPatterns, isInjective, isSurjective, postprocess, priority }
  let env ← getEnv
  let newEnv := externalEquivalenceCache.addEntry env (key, value)
  setEnv newEnv

/-- Retrieve an external equivalence, if it exists. -/
def getExternalEquivalence (name : ExternalEquivalenceKey) : CommandElabM (Option ExternalEquivalence) := do
  let env ← getEnv
  let cache := externalEquivalenceCache.getState env
  return cache.get? name

def getExternalEquivalencesForCategory (cat : Name) : CommandElabM (Array (ExternalEquivalence)) := do
  let env ← getEnv
  let cache := externalEquivalenceCache.getState env
  let mut out := #[]
  for (_, v) in cache.toList do
    if v.syntaxCategory == cat then
      out := out.push v
  out := out.qsort (fun v1 v2 => match (v1.exprPattern, v2.exprPattern) with
    | (.eager e1, .eager e2) => e1.expr.expr.hash < e2.expr.expr.hash
    | _ => false) -- For determinism
  out := out.qsort (fun v1 v2 => v1.priority > v2.priority) -- Higher priority first
  return out


/-- The signature for our (partial) elaboration functions. Normal `TermElab`s won't do here, since ideally we want to do some stuff in between recognizing which syntax is in the "blank" spots and fully elaborating it, which is hard to do without specifying everything up front when its created or spamming a bunch of `ref`s. -/
abbrev ExternalElabSignature := Syntax → Option Expr → TermElabM (ExternalEquivalenceKey × List (Name × Syntax) × List (Name × Syntax))


unsafe def mkTermElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute ExternalElabSignature) :=
  mkElabAttribute ExternalElabSignature `builtin_external_elab `external_elab `Lean.Parser.Term `ExternalElabSignature "term" ref

/-- An attribute to tag external elaborators for later access. All currently registered external elaborators can be accessed via `externalElabAttribute.getEntries e k` for `e` the relevant environment and `k` the name they were tagged with (usually the name of the SyntaxNodeKind they correspond to). -/
initialize externalElabAttribute : KeyedDeclsAttribute ExternalElabSignature ←
  unsafe mkTermElabAttributeUnsafe decl_name%
