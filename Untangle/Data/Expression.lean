import Lean.Data.HashMap
import Lean.Elab.Tactic
import Lean.Expr
import Lean.Data.Json.FromToJson
import Mathlib.Data.String.Defs
import Mathlib.Init.Data.List.Instances
import Mathlib.Init.Control.Combinators

open Lean Meta Server Expr

inductive ExpressionType where
  | Functor
  | Morphism
  | NaturalTransformation
  | Category
  | Object

inductive Expression : ExpressionType → Type where
  | Category (expression: Expr) : Expression Category
  | Object (expression: Expr) : Expression ExpressionType.Object
  | Morphism (expression: Expr) (source: Expression ExpressionType.Object) (target: Expression ExpressionType.Object) : Expression ExpressionType.Morphism
  | NaturalTransformation (expression: Expr) (source: Expression ExpressionType.Functor) (target: Expression ExpressionType.Functor) : Expression NaturalTransformation
  | NaturalTransformationComponent (naturalTransformation : Expression ExpressionType.NaturalTransformation) (object : Expression ExpressionType.Object) (source : Expression ExpressionType.Functor) (target : Expression ExpressionType.Functor): Expression ExpressionType.Morphism
  | Functor (expression: Expr) (source: Expression ExpressionType.Object) (target: Expression ExpressionType.Object) : Expression ExpressionType.Functor
  | FunctorComposition (left : Expression ExpressionType.Functor) (right : Expression ExpressionType.Functor) : Expression ExpressionType.Functor
  | MorphismComposition (expression : Expr) (first: Expression ExpressionType.Morphism) (second: Expression ExpressionType.Morphism) : Expression ExpressionType.Morphism
  | LiftObject (functor : Expression ExpressionType.Functor) (object : Expression ExpressionType.Object) : Expression ExpressionType.Object
  | LiftMap (functor : Expression ExpressionType.Functor) (arrow : Expression ExpressionType.Morphism) : Expression ExpressionType.Morphism
  | PlainExpression (expression : Expr) : Expression _
  | DebugExpression (expression : Expr) : Expression _
  | DebugString (s: String) : Expression _
  deriving Repr

namespace Expression
  def countFunctorApplications : Expression ExpressionType.Functor → Nat
    | Functor _ _ _ => 1
    | FunctorComposition left right => left.countFunctorApplications + right.countFunctorApplications
    | _ => unreachable!

  def countObjectLifts : Expression ExpressionType.Object → Nat
    | Object  _ => 0
    | LiftObject _ object => 1 + object.countObjectLifts
    | _ => unreachable!

  def source : Expression ExpressionType.Morphism → Option (Expression ExpressionType.Object)
    | Morphism _ source _ => source
    | MorphismComposition _ f g => f.source
    | _ => unreachable!

  def target : Expression ExpressionType.Morphism → Option (Expression ExpressionType.Object)
    | Morphism _ _ target => target
    | MorphismComposition _ f g => g.target
    | _ => unreachable!


end Expression

def morphismFromTo : Expression ExpressionType.Morphism → Expression ExpressionType.Object → Expression ExpressionType.Object → Expression ExpressionType.Morphism
  | (Expression.Morphism morphism _ _), X, Y => Expression.Morphism morphism X Y
  | e, _, _ => e


def natTransFromTo : Expression ExpressionType.NaturalTransformation → Expression ExpressionType.Functor → Expression ExpressionType.Functor → Expression ExpressionType.NaturalTransformation
  | (Expression.NaturalTransformation transformation _ _), F, G => Expression.NaturalTransformation transformation F G
  | e, _, _ => e

instance : ToString (Expression α) := ToString.mk reprStr
