/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.MapComposition

/-!
# Restriction of singular simplex summands to a subspace

A degreewise projection retains exactly the simplices whose entire image lies
in the subspace. This is a module projection, not an asserted chain projection.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits
open scoped Simplicial
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable
variable {X : Type u} [TopologicalSpace X]

/-- The continuous inclusion of a subspace. -/
def subspaceInclusion (U : Set X) : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- Restrict a simplex whose whole range lies in the subspace. -/
def subspaceSimplex (U : Set X) {n : SimplexCategory} (σ : SingularSimplex X n)
    (hσ : Set.range σ ⊆ U) : SingularSimplex U n :=
  ⟨fun t ↦ ⟨σ t, hσ ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩

@[simp]
theorem subspaceInclusion_comp_subspaceSimplex (U : Set X) {n : SimplexCategory}
    (σ : SingularSimplex X n) (hσ : Set.range σ ⊆ U) :
    (subspaceInclusion U).comp (subspaceSimplex U σ hσ) = σ := by
  ext t
  rfl

/-- Retain a simplex summand precisely when it lies in the subspace. -/
def subspaceModuleProjection (U : Set X) (A : System.{u, u} X) (n : SimplexCategory) :
    chainModule A n ⟶ chainModule (pullback (subspaceInclusion U) A) n := by
  classical
  exact Sigma.desc fun σ ↦ if hσ : Set.range σ ⊆ U then
    chainInclusion (pullback (subspaceInclusion U) A) (subspaceSimplex U σ hσ) else 0

@[reassoc (attr := simp)]
theorem chainInclusion_subspaceModuleProjection (U : Set X) (A : System.{u, u} X)
    {n : SimplexCategory} (σ : SingularSimplex X n) :
    chainInclusion A σ ≫ subspaceModuleProjection U A n =
      if hσ : Set.range σ ⊆ U then
        chainInclusion (pullback (subspaceInclusion U) A) (subspaceSimplex U σ hσ) else 0 := by
  classical
  exact Sigma.ι_comp_desc _ _

/-- Subspace inclusion followed by restriction retains each original summand. -/
theorem subspaceInclusion_projection (U : Set X) (A : System.{u, u} X)
    (n : SimplexCategory) :
    pushforwardModuleMap (subspaceInclusion U) A n ≫ subspaceModuleProjection U A n = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro σ
  have hσ : Set.range ((subspaceInclusion U).comp σ) ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact (σ t).property
  change chainInclusion (pullback (subspaceInclusion U) A) σ ≫
      (pushforwardModuleMap (subspaceInclusion U) A n ≫ subspaceModuleProjection U A n) =
    chainInclusion (pullback (subspaceInclusion U) A) σ ≫ 𝟙 _
  rw [chainInclusion_pushforwardModuleMap_assoc, chainInclusion_subspaceModuleProjection,
    dite_eq_left hσ, Category.comp_id]
  rfl

end FundamentalGroupoid.LocalCoefficients
