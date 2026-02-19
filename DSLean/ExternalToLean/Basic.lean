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
import Lean.Meta

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq
open Std.Internal.Parsec Std.Internal.Parsec.String
open Std.Internal Parser Command Syntax Quote

/-- Carries user-defined additional options for external equivalences (each line of the DSL). -/
structure ExternalEquivalenceOptions where
  rightAssociative : Bool := false
  precedence : Int := 0
  priority : Int := 0
deriving Inhabited, Repr
declare_command_config_elab elabExternalEquivalenceOptions ExternalEquivalenceOptions
