/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.HomotopyInvariance

/-!
Adapted from `Quillen/Topology/LocalCoefficients/RelativeHomology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual coefficient maps.

 # Actual local homology maps with specified coefficient morphisms -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The actual spatial homology map preceded by the specified coefficient morphism. -/
def relativeHomologyMap (f : C(X, Y)) {A : System.{u, u} X} {B : System.{u, u} Y}
    (η : A ⟶ pullback f B) (n : ℕ) : homology A n ⟶ homology B n :=
  coefficientHomologyMap η n ≫ pushforwardHomologyMap f B n

/-- A genuine homotopy identifies the two maps exactly when its specified
transport identifies the two coefficient morphisms. -/
theorem relativeHomologyMap_homotopy {f g : C(X, Y)} (H : f.Homotopy g)
    {A : System.{u, u} X} {B : System.{u, u} Y}
    (η : A ⟶ pullback f B) (θ : A ⟶ pullback g B)
    (h : η ≫ (homotopyPullbackIso H B).hom = θ) (n : ℕ) :
    relativeHomologyMap f η n = relativeHomologyMap g θ n := by
  unfold relativeHomologyMap
  rw [pushforwardHomologyMap_homotopy H]
  change coefficientHomologyMap η n ≫
    (coefficientHomologyMap (homotopyPullbackIso H B).hom n ≫ _) = _
  rw [← Category.assoc, ← coefficientHomologyMap_comp, h]

/-- Composition retains the exact pullback-composition conversion. -/
@[reassoc]
theorem relativeHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z))
    {A : System.{u, u} X} {B : System.{u, u} Y} {D : System.{u, u} Z}
    (η : A ⟶ pullback f B) (θ : B ⟶ pullback g D) (n : ℕ) :
    relativeHomologyMap f η n ≫ relativeHomologyMap g θ n =
      relativeHomologyMap (g.comp f)
        (η ≫ pullbackMap f θ ≫ (pullbackCompositionIso f g D).inv) n := by
  simp only [relativeHomologyMap, coefficientHomologyMap_comp,
    pushforwardHomologyMap_comp, Category.assoc]
  rw [← pushforwardHomologyMap_coefficient_naturality_assoc]
  rw [← coefficientHomologyMap_comp_assoc (pullbackCompositionIso f g D).inv
    (pullbackCompositionIso f g D).hom n, Iso.inv_hom_id,
    coefficientHomologyMap_id, Category.id_comp]

end FundamentalGroupoid.LocalCoefficients
