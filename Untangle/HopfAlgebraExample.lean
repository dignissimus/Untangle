
import Aesop
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Monad.Basic
import Untangle.Untangle
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Init.Data.List.Instances
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Bialgebra
import Mathlib.RingTheory.HopfAlgebra

open Untangle TensorProduct Coalgebra HopfAlgebra

example [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] :
  (LinearMap.mul' R A)
  ∘ₗ (LinearMap.mul' R A).lTensor A
  ∘ₗ (TensorProduct.assoc R A A A).toLinearMap
  ∘ₗ comul.rTensor A
  ∘ₗ (LinearMap.mul' R A).rTensor A
  ∘ₗ antipode.lTensor (A ⊗[R] A)
  ∘ₗ (TensorProduct.assoc R A A A).symm
  ∘ₗ comul.lTensor A

  =
  (LinearMap.mul' R A)
  ∘ₗ (TensorProduct.comm R A A)
  ∘ₗ (LinearMap.mul' R A).lTensor A
  ∘ₗ (TensorProduct.assoc R A A A)
  ∘ₗ comul.rTensor A


  := by with_panel_widgets [UntangleHopf] {

  }
