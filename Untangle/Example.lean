import Aesop
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Monad.Basic
import Untangle.Untangle
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Init.Data.List.Instances

open CategoryTheory Category

open Untangle

variable [Category C] (T : Monad C)

-- Apply the associativity law for the μ naturl transformation
example : (Monad.μ T).app (T.obj X) ≫ (Monad.μ T).app X = T.map ( (Monad.μ _).app _ ) ≫ (Monad.μ _).app _ := by with_panel_widgets [Untangle] {

  -- Click the two μ natural transformations to apply the associativity law
  -- Place cursor on this line


}

-- Apply the Monad unit law
example : (Monad.η T).app (T.obj X) ≫ (Monad.μ T).app X = (CategoryStruct.id $ T.obj X) := by with_panel_widgets [Untangle] {

  -- Click the η transformation and the μ transformation
  -- Place cursor on this line

}

-- Apply the Monad unit law on the left and on the right
example : T.map (T.η.app X) ≫ T.μ.app _ = (Monad.η T).app (T.obj X) ≫ (Monad.μ T).app _ := by with_panel_widgets [Untangle] {

    -- 1. Click η and μ to apply the unit law for the Monad natural transformations
    -- 2. Do the same on the other side of the diagram
    -- Place cursor on this line try simp;



  }

-- The same thing as above but for T (T X)
example : T.η.app (T.obj $ T.obj X) ≫ T.μ.app _ = (CategoryStruct.id $ T.obj $ T.obj X) := by with_panel_widgets [Untangle] {
  -- Place cursor on this line

}


lemma filter_join_eq_join_filter'
  [Category C]
  {T : Monad C}
  {X : C}
  {guard' : X ⟶ T.obj X }
  : T.μ.app _ ≫ T.map guard' ≫ T.μ.app _ = T.map (T.map guard') ≫ T.map (T.μ.app _) ≫ T.μ.app _
  := by with_panel_widgets [Untangle] {
    -- 1. Click guard' and Monad.μ T to swap the order using the naturality of μ
    -- 2. Click back so that the cursor is in the editor to update the diagram
    -- 3. click the two Monad.μ boxes to apply the associativity law

    -- Put cursor on this line


  }

-- TODO:
--  In the future I'd like to search through hypotheses and generate
--  rewrite rules for morphisms in the category
example
  [Category C]
  {X Y Z W : C}
  (x : X ⟶ Y)
  {y : Y ⟶ Z}
  {z z' : Z ⟶W}
  {w : X ⟶ Z}
  {h : x ≫ y = w}
  {h' : y ≫ z = y ≫ z'}
  : x ≫ y ≫ z = w ≫ z'
  := by with_panel_widgets [Untangle] {
    rw [h']
    rw [reassoc_of% h]
  }


open scoped CategoryTheory.Monad

-- The below examples cause errors

-- This errors because I haven't implemented lifting the composition of morphisms
-- For example T.map (f ≫ g) errors but T.map f ≫ T.map g will work
lemma _filter_join_eq_join_filter'
  [Category C]
  {T : CategoryTheory.Monad C}
  {X : C}
  {guard' : X ⟶ T.obj X }
  :
    T.μ.app _ ≫ T.map guard' ≫ T.μ.app _ = T.map (T.map guard' ≫ T.μ.app _) ≫ T.μ.app _
   :=
  by with_panel_widgets[Untangle]
    rw [← reassoc_of% T.μ.naturality _]
    rw [← T.comp_map]
    simp
    have : (Monad.μ T).app (T.obj X) ≫ (Monad.μ T).app _ = T.map ((Monad.μ T).app X) ≫ (Monad.μ T).app _ := by with_panel_widgets [Untangle]
      rw [T.assoc]
    rw [Monad.assoc]

def listMonad := ofTypeMonad List
def guard' (p : X → Bool) : X ⟶ List X
  | x => if p x then [x] else []
def join' {X} := listMonad.μ.app X
def filter' (p : X → Bool) : List X ⟶ List X := listMonad.map (guard' p) ≫ join'
#eval filter' (λ x ↦ x % 2 == 0) [1, 2, 3, 4, 5, 6]

example : filter' p ∘ join' = join' ∘ List.map (filter' p) := by
  unfold filter'
  unfold join'
  have {X Y Z : Type} {f : X ⟶ Y} {g : Y ⟶ Z} : g ∘ f  = f ≫ g := by rfl
  repeat rw [this]
  apply _filter_join_eq_join_filter'

-- TODO: This errors because I haven't implemented parsing goals that contain let clauses
lemma filter_join_eq_join_filter
  [Category C]
  {T : Monad C}
  {X : C}
  {guard' : X ⟶ T.obj X }
  :
    let filter := T.map guard' ≫ T.μ.app _;
    T.μ.app _ ≫ filter = T.map filter ≫ T.μ.app _
   := by with_panel_widgets [Untangle]
    let filter := T.map guard' ≫ T.μ.app _;
    simp [filter]
    rw [← reassoc_of% T.μ.naturality _]
    rw [Monad.assoc]


-- TODO:
-- This errors because I haven't yet implemented working with goals
--  that contain contain explicit functor composition
-- For example (F ⋙ G).map f will error
example
  [Category C]
  [Category D]
  {F : C ⥤ D}
  {T : C ⥤ C}
  {X : C}
  {Y : C}
  {h : X ⟶ Y}
  {a : T.obj X ⟶ X}
  {a' : T.obj Y ⟶ Y}
  {hT : T.map h ≫ a' = a ≫ h}
  {T' : D ⥤ D}
  {α : NatTrans (F ⋙ T') (T ⋙ F)}
  : α.app X ≫ F.map a ≫ F.map h
    = (F ⋙ T').map h ≫ α.app Y ≫ F.map a'
   := by with_panel_widgets [Untangle]

    rw [← F.map_comp]
    nth_rewrite 1 [← hT]
    rw [F.map_comp]
    rw [← reassoc_of% α.naturality h]
    simp


-- This example also causes an error due to functor composition as above: i.e. F ⋙ T
example
  [Category C]
  [Category D]
  [MonoidalCategory C]
  [MonoidalCategory D]
  {F : C ⥤ D}
  {T : C ⥤ C}
  {X : C}
  {Y : C}
  {h : X ⟶ Y}
  {a : T.obj X ⟶ X}
  {a' : T.obj Y ⟶ Y}
  {hT : T.map h ≫ a' = a ≫ h}
  {T' : D ⥤ D}
  {α : NatTrans (F ⋙ T') (T ⋙ F)}
  : T ⋙ T ⋙ T  = (T ⋙ T) ⋙ T := by with_panel_widgets [Untangle]
    skip
    sorry


example
  [Category C]
  [Category D]
  { F : C ⥤ D }
  { G : D ⥤ C }
  { adjunction : F ⊣ G }
  : sorry := by
    sorry
