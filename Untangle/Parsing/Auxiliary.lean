import Lean.Data.HashMap
import Lean.Elab.Tactic
import Lean.Expr
import Lean.Data.Json.FromToJson
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod
import Mathlib.Init.Data.List.Instances
import Mathlib.Init.Control.Combinators
import Mathlib.Data.String.Defs
import Untangle.Data.Expression

open Lean Meta Server Expr

def orElse (f g : α → Option β) : α → Option β
  | x => (f x).orElse (λ _ ↦ g x)

infixl:65 " or " => orElse
macro_rules
  | `(fail) => `(do ← none)


def unknown : Expression α := Expression.DebugString "?"

/- Utilities -/
def withAppAux? (k : Expr → Array Expr → α) : Expr → Array Expr → Nat → Option α
  | app f a, as, i => some $ withAppAux k f (as.set! i a) (i-1)
  | _, _, _ => none

@[inline] def withApp? (e : Expr) (k : Expr → Array Expr → α) : Option α :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  withAppAux? k e (mkArray nargs dummy) (nargs-1)

/-def constName (e : Expr) : Name :=
  e.constName?.getD Name.anonymous-/

def getAppFnArgs? (e : Expr) : Option $ Name × Array Expr :=
  withApp? e λ e a => (constName e, a)
