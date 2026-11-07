/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Monoidal/Action/LinearComposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Identity and composition of genuine lax linear functors -/

@[expose] public section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open CategoryTheory.Functor.LaxLeftLinear
universe u v u₁ v₁ u₂ v₂ u₃ v₃
namespace CategoryTheory.Functor.LaxLeftLinear
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  {V : Type u₃} [Category.{v₃} V] [MonoidalLeftAction C V]

/-- The identity lineator retains the actual identity arrow. -/
@[instance_reducible]
def identity : (𝟭 D).LaxLeftLinear C where
  μₗ _ _ := 𝟙 _
  μₗ_naturality_left _ _ := by simp
  μₗ_naturality_right _ _ _ _ := by simp
  μₗ_associativity _ _ _ := by simp
  μₗ_unitality _ := by simp

/-- The composite lineator is the specified composite of the original lineators. -/
@[instance_reducible]
def composition (F : D ⥤ E) (G : E ⥤ V) [F.LaxLeftLinear C] [G.LaxLeftLinear C] :
    (F ⋙ G).LaxLeftLinear C where
  μₗ s X := μₗ G s (F.obj X) ≫ G.map (μₗ F s X)
  μₗ_naturality_left f X := by
    dsimp
    rw [← Category.assoc, μₗ_naturality_left, Category.assoc,
      ← G.map_comp, μₗ_naturality_left, G.map_comp]
    simp only [Category.assoc]
  μₗ_naturality_right s _ _ f := by
    dsimp
    rw [← Category.assoc, μₗ_naturality_right, Category.assoc,
      ← G.map_comp, μₗ_naturality_right, G.map_comp]
    simp only [Category.assoc]
  μₗ_associativity s t X := by
    dsimp
    rw [Category.assoc, ← G.map_comp, μₗ_associativity, G.map_comp, G.map_comp,
      ← Category.assoc, μₗ_associativity]
    simp only [Category.assoc, MonoidalLeftAction.actionHomRight_comp]
    rw [μₗ_naturality_right_assoc]
  μₗ_unitality X := by
    dsimp
    rw [Category.assoc, ← G.map_comp, ← μₗ_unitality, ← μₗ_unitality]

end CategoryTheory.Functor.LaxLeftLinear
