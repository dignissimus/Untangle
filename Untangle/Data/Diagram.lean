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
import Untangle.Parsing.Auxiliary

open Lean Meta Server Expr
open ProofWidgets

namespace Diagram

inductive FunctorLike where
  | Functor (expr : Expr)
  | Object (expr : Expr)
deriving Repr, BEq



inductive TransformationLike where
  | NaturalTransformation (expr : Expr)
  | Morphism (expr : Expr)
deriving Repr, BEq



structure Transformation where
  label : TransformationLike
  -- Inclusive range
  left : Nat
  right : Nat

  -- How many outputs this transformation has
  numberOfOutputs : Nat
deriving Repr

structure DiagramComponent where
  inputs : List FunctorLike
  transformation: Transformation
  outputs : List FunctorLike
  location : ℕ
  functorApplications : ℕ := 0
deriving Repr

abbrev Diagram := List DiagramComponent

structure GraphicalLanguage where
  parseExpression : Expr → Option (Expression ExpressionType.Morphism)
  generateTactic :
    (goal : Widget.InteractiveGoal)
    → (first : Diagram.DiagramComponent)
    → (second : Diagram.DiagramComponent)
    → RequestM $ Option (List String)
  isIdentity : Expr → Bool
  renderExpression : (location : ℕ) → Expression ExpressionType.Morphism → Option Diagram

namespace FunctorLike
  def isIdentity : FunctorLike → Diagram.GraphicalLanguage →  Bool
    | Functor functor, language => language.isIdentity functor
    | _, _ => false
end FunctorLike

namespace TransformationLike
  def expression : TransformationLike → Expr
    | NaturalTransformation expression => expression
    | Morphism expression => expression

def isIdentity (α : TransformationLike)  (language : Diagram.GraphicalLanguage): Bool := language.isIdentity α.expression
end TransformationLike

namespace Transformation
  def range (left : Nat) (right : Nat) :=  List.map Prod.fst ∘ List.enumFrom left $ List.range (right - left + 1)
  def inputs (α : Transformation) := range α.left α.right
  def isIdentity (α : Transformation) := α.label.isIdentity

  def numberOfInputs (α : Transformation) := α.right - α.left + 1
  def outputStart (α : Transformation) := α.left
  def outputEnd (α : Transformation) := α.left + α.numberOfOutputs - 1
  def outputs(α : Transformation) := range α.outputStart α.outputEnd
end Transformation

instance : ToString (DiagramComponent) := ToString.mk reprStr

partial def simplifyFunctor (expression : Expr) : Expr :=
    match getAppFnArgs? expression with
        | some (`CategoryTheory.Functor.toPrefunctor, #[_, _, _, _, functor]) => simplifyFunctor functor
        | some (`CategoryTheory.Monad.toFunctor, #[_, _, monad]) => simplifyFunctor $ monad
        -- TODO maybe
        | _ => expression

def raw : Expression α → Expr
  | .Object object => object
  | .Morphism morphism _ _ => morphism
  | .NaturalTransformation transformation _ _ => transformation
  -- | NaturalTransformationComponent (naturalTransformation : Expression ExpressionType.NaturalTransformation) (object : Expression ExpressionType.Object) (source : Expression ExpressionType.Functor) (target : Expression ExpressionType.Functor): Expression ExpressionType.Morphism
  | .Functor functor _ _ => simplifyFunctor functor
  | _ => Expr.const `Eq [.succ .zero]
  -- | FunctorComposition (left : Expression ExpressionType.Functor) (right : Expression ExpressionType.Functor) : Expression ExpressionType.Functor
  -- | MorphismComposition (first: Expression ExpressionType.Morphism) (second: Expression ExpressionType.Morphism) : Expression ExpressionType.Morphism
  -- | LiftObject (functor : Expression ExpressionType.Functor) (object : Expression ExpressionType.Object) : Expression ExpressionType.Object
  -- | LiftMap (functor : Expression ExpressionType.Functor) (arrow : Expression ExpressionType.Morphism) : Expression ExpressionType.Morphism
  -- | PlainExpression (expression : Expr) : Expression _
  -- | DebugExpression (expression : Expr) : Expression _
  -- | DebugString (s: String) : Expression _
namespace DiagramComponent

def expression (d : DiagramComponent) : Expr := d.transformation.label.expression

def swap (d : DiagramComponent) : DiagramComponent := {d with inputs := d.outputs, outputs := d.inputs}

def shiftLeft (d : DiagramComponent) (shift : Nat) : DiagramComponent := {
    d with
      transformation.left := d.transformation.left - shift
      transformation.right := d.transformation.right - shift
}

def shiftRight (d : DiagramComponent) (shift : Nat) : DiagramComponent := {
    d with
      transformation.left := d.transformation.left + shift
      transformation.right := d.transformation.right + shift
}

abbrev shift := shiftRight


-- Major TODO
def applyFunctor (d : DiagramComponent) (functor : Expression ExpressionType.Functor) : DiagramComponent :=
  let fexp := raw functor;
  {
    d with
    inputs := d.inputs ++ [FunctorLike.Functor fexp]
    outputs := d.outputs ++ [FunctorLike.Functor fexp]
    functorApplications := d.functorApplications + 1
}

def isNaturalTransformation : DiagramComponent → Bool
  | {transformation ..} => match transformation.label with
    | .NaturalTransformation _ => True
    | _ => False

end DiagramComponent

end Diagram
