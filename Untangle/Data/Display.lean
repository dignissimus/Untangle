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


open Lean Meta Server Expr
open ProofWidgets

-- TODO: Excessive imports

inductive Side where
  | Left
  | Right
deriving Repr, RpcEncodable

namespace Side
def toNat : Side → ℕ
  | Left => 1
  | Right => 2
end Side

instance : ToString Side where
  toString : Side → String
    | .Left => "Left"
    | .Right => "Right"

instance : ToJson Side := ToJson.mk (Json.str ∘ toString)
