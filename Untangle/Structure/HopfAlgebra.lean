import Lean.Expr

import Untangle.Data.Diagram
import Untangle.Data.Expression
import Untangle.Parsing.Auxiliary

import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Bialgebra
import Mathlib.RingTheory.HopfAlgebra

import Mathlib.Algebra.Module.Equiv

open Lean Diagram

namespace Expression
  def  _expr : Expression ExpressionType.Morphism → Expr
    | Expression.Morphism expr _ _ => expr
    | Expression.LeftTensor _ _ f => f._expr
    | Expression.RightTensor _ _ f => f._expr
    | _ => unreachable!
end Expression
mutual
  partial def parseMap (e : Expr) : Option (Expression ExpressionType.Morphism) :=
    match getAppFnArgs? e with
      | .some (``LinearMap.id, #[_, M, _, _, _]) =>
        return Expression.Morphism e (Expression.Object M) (Expression.Object M)
      | .some (``LinearMap.mul', #[R, A, _, _, _, _, _]) =>
        return Expression.Morphism e (Expression.ObjectProduct (← parseModule A) (← parseModule A)) (← parseModule A)
      | .some (``TensorProduct.assoc, #[R, _, M, N, P, _, _, _, _, _, _]) =>
        return Expression.Morphism e
          (Expression.ObjectProduct
            (Expression.ObjectProduct (← parseModule M) (← parseModule N))
            (← parseModule P))
          (Expression.ObjectProduct
            (← parseModule M)
            (Expression.ObjectProduct (← parseModule N) (← parseModule P)))
      | .some (``LinearMap.comp, #[_, _, _, M₁, M₂, M₃, _, _, _, _, _, _, _, _, _, _, _, _, _, f, g]) =>
        return Expression.MorphismComposition e (← parseMap f) (← parseMap g)
      | .some (`TensorProduct.comm, #[_, _, M, N, _, _, _, _]) =>
        return Expression.Morphism e
          (Expression.ObjectProduct (← parseModule M) (← parseModule N))
          (Expression.ObjectProduct (← parseModule N) (← parseModule M))
      | .some (``CoalgebraStruct.comul, #[R, A, _, _, _, _]) =>
        return Expression.Morphism e
          (← parseModule A)
          (Expression.ObjectProduct (← parseModule A) (← parseModule A))
      | .some (``TensorProduct.map, #[R, _, M, N, P, Q, _, _, _, _, _, _, _, _, f, g]) =>
        return Expression.MorphismProduct e
          (← parseMap f)
          (← parseMap g )
      | .some (``TensorProduct.lift, #[_, _, _, _, _, _, _, _, _, _, _, _, _, _, _]) =>
        .none
      | .some (``LinearMap.lTensor, #[R, _, M, N, P, _, _, _, _, _, _, f]) =>
        return Expression.LeftTensor e (← parseModule M) (← parseMap f)
      | .some (``LinearMap.rTensor, #[R, _, M, N, P, _, _, _, _, _, _, f]) =>
        return Expression.RightTensor e (← parseModule M) (← parseMap f)
      | .some (``HopfAlgebra.antipode, #[R, A, _, _, _]) =>
        return Expression.Morphism e
          (← parseModule A)
          (← parseModule A)
      | .some (``LinearEquiv.symm, #[_, _, _, _, _, _, _, _, _, _, _, _, _, _, f]) => do
        match (← parseMap f) with
          | Expression.Morphism _ source target =>  Expression.Morphism f target source
          | _ => unreachable!

      | .some (``LinearEquiv.toLinearMap, #[_, _, _, _, _, _, _, _, _, _, _, _, _, _, f]) => do
        (← parseMap f)

      | _ => .none


  partial def parseModule (e : Expr) : Option (Expression ExpressionType.Object) :=
    match getAppFnArgs? e with
      | .some (`TensorProduct, #[R, _, M, N, _, _, _, _]) => return Expression.ObjectProduct (← parseModule M) (← parseModule N)
      | _ => return Expression.Object e

  -- TODO: Extract domain and codomain from type information
  partial def parseArbitraryMap (e : Expr) : Option (Expression ExpressionType.Morphism) :=
    .none
    -- return Expression.Morphism e (← parseModule sorry) (← parseModule sorry)

  partial def parseExpression : Expr → Option (Expression ExpressionType.Morphism) :=
    parseMap
    or parseArbitraryMap

end

def renderInput : Expression ExpressionType.Object → List FunctorLike
  | Expression.Object object => [FunctorLike.Object object]
  | Expression.ObjectProduct left right => renderInput left ++ renderInput right
  | _ => unreachable!

def renderInputs : Expression ExpressionType.Morphism → List FunctorLike
  | Expression.Morphism _ source _ => renderInput source
  | Expression.LeftTensor _ M f  => renderInput M ++ renderInputs f
  | Expression.RightTensor _ N f => renderInputs f ++ renderInput N
  | _ => unreachable!

def leftSkip : Expression ExpressionType.Morphism → ℕ
  | Expression.LeftTensor _ M f  => (renderInput M).length + leftSkip f
  | Expression.RightTensor _ _ f => leftSkip f
  | _ => 0

def rightSkip : Expression ExpressionType.Morphism → ℕ
  | Expression.LeftTensor _ _ f => leftSkip f
  | Expression.RightTensor _ M f  => (renderInput M).length + leftSkip f
  | _ => 0

def renderOutputs : Expression ExpressionType.Morphism → List FunctorLike
  | Expression.Morphism _ _ target => renderInput target
  | Expression.LeftTensor _ M f  => renderInput M ++ renderOutputs f
  | Expression.RightTensor _ N f => renderOutputs f ++ renderInput N
  | _ => unreachable!

def countObjects : Expression ExpressionType.Object → ℕ
  | Expression.Object _ => 1
  | Expression.ObjectProduct left right => countObjects left + countObjects right
  | _ => unreachable!


partial def constructDiagramComponent (location : ℕ) : Expression ExpressionType.Morphism → List DiagramComponent
  | Expression.Morphism expr source target => do
    let inputs := renderInput source
    let outputs := renderInput target

    return {
      inputs := inputs
      transformation := {
        label := TransformationLike.Morphism expr,
        left := 0,
        right := inputs.length - 1,
        numberOfOutputs := outputs.length
      }
      location
      outputs := outputs
    }

  -- TODO: Perhaps it's easier to replace all instances of ⟨f, g⟩ as the composition of lTensor and rTensor
  | Expression.MorphismProduct e f g => constructDiagramComponent location f ++ constructDiagramComponent location g

  | f@(Expression.LeftTensor expr M f') => do
    let inputs := renderInputs f
    let outputs := renderOutputs f
    return {
      inputs := inputs
      outputs := outputs
      transformation := {
        label := TransformationLike.Morphism f'._expr
        left := (renderInput M).length + leftSkip f'
        right := inputs.length - rightSkip f' - 1
        numberOfOutputs := outputs.length - (renderInput M).length - leftSkip f' - rightSkip f'
      }
      location
    }

  | f@(Expression.RightTensor expr N f') =>
    let inputs := renderInputs f
    let outputs := renderOutputs f
    return {
      inputs := inputs
      outputs := outputs
      transformation := {
        label := TransformationLike.Morphism f'._expr
        left := leftSkip f'
        right := (renderInputs f').length - rightSkip f' - 1
        numberOfOutputs := outputs.length - (renderInput N).length - leftSkip f' - rightSkip f'
      }
      location
    }

  | e => panic! s!"Unreachable: {e}"

def renderExpression (location : ℕ): Expression ExpressionType.Morphism → Option Diagram
  | Expression.MorphismComposition  _ left right => do
    let first ← renderExpression location right
    let last ← first.getLast?
    let offset := last.location + 1
    let second ← renderExpression offset left
    return first ++ second
  | morphism => constructDiagramComponent location morphism

def hopf : Diagram.GraphicalLanguage where
  parseExpression := parseExpression
  generateTactic _ _ _ := return .none
  isIdentity (e : Expr) : Bool :=
    match getAppFnArgs? e with
      | .some (`LinearMap.id, #[_, _, _, _, _]) => true
      | .some (``TensorProduct.assoc, #[R, _, M, N, P, _, _, _, _, _, _]) => true
      | _ => false
  isBraid (e : Expr) : Bool :=
    match getAppFnArgs? e with
      | .some (`TensorProduct.comm, #[_, _, M, N, _, _, _, _]) => true
      | _ => false
  renderExpression := renderExpression
  name := "Hopf"

-- Lemmas
open TensorProduct HopfAlgebra Bialgebra Coalgebra LinearMap
lemma assoc_inj
[CommSemiring R]
[AddCommMonoid A]
[AddCommMonoid B]
[AddCommMonoid C]
[AddCommMonoid D]
[AddCommMonoid E]
[AddCommMonoid F]
[AddCommMonoid G]
[Module R A]
[Module R B]
[Module R C]
[Module R D]
[Module R E]
[Module R F]
[Module R G]
{f : A →ₗ[R] B}
{i : A →ₗ[R] B}
{g : C →ₗ[R] D}
{j : C →ₗ[R] D}
{h : E →ₗ[R] F}
{k : E →ₗ[R] F}
: map (map f g) h = map (map i j) k → map f (map g h) = map i (map j k) := by
  intro hyp
  ext x y z
  simp
  have hyp' := (TensorProduct.map_tmul (map f g) h (x ⊗ₜ[R] y) z).symm
  rw [TensorProduct.map_tmul f g x y] at hyp'
  rw [hyp] at hyp'
  rw [TensorProduct.map_tmul (map i j) k (x ⊗ₜ[R] y) z] at hyp'
  rw [TensorProduct.map_tmul i j x y] at hyp'
  repeat rw [← TensorProduct.assoc_tmul]
  rw [hyp']

lemma mul'_comp_comul [CommSemiring R] [Semiring A] [Bialgebra R A] : LinearMap.mul' R _ ∘ₗ  TensorProduct.map comul comul = comul ∘ₗ LinearMap.mul' R A := by
  ext
  simp

lemma mul'_comp_counit [CommSemiring R] [Semiring A] [B : Bialgebra R A] : LinearMap.mul' R _ ∘ₗ  TensorProduct.map B.counit B.counit = B.counit ∘ₗ LinearMap.mul' R _:= by
  ext
  simp

lemma comul_comp_mul' [CommSemiring R] [Semiring A] [B : Bialgebra R A] : B.comul ∘ₗ LinearMap.mul' R A = LinearMap.mul' R _ ∘ₗ TensorProduct.map comul comul := by
  ext
  simp

-- TODO: Use the mathlib rTensor_comp_lTensor instead of this one
theorem rTensor_comp_lTensor' [CommSemiring R] [CommSemiring A] [H : HopfAlgebra R A] : map H.comul H.comul = (H.comul.rTensor (A ⊗[R] A)).comp (H.comul.lTensor A) := by
  simp only [rTensor_comp_lTensor]
