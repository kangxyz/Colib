/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Functoriality
public import Colib.Topology.FilteredRealization.Compact
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
Adapted from `Quillen/Topology/LocalCoefficients/FilteredChains.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the native singular
chain complex, actual transition maps, and coefficient transports.

# Actual local chains in filtered realization colimits

Compactness of the standard simplex gives exact lifts of singular simplices
through original stages. Consequently the original stage pushforwards jointly
generate the local chain module, for arbitrary coefficients on the colimit.
Equality of stage simplices is detected at a later stage. These statements are
chain-level inputs to a colimit comparison, not an assumed homology theorem.
-/

@[expose] public section

open Convexity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
include hc

/-- Every actual singular simplex factors through an original filtered stage. -/
theorem filtered_simplex_factors (n : SimplexCategory) (σ : SingularSimplex |c.pt| n) :
    ∃ j, ∃ τ : SingularSimplex |F.obj j| n,
      (SSet.toTop.map (c.ι.app j)).hom.comp τ = σ :=
  Topology.FilteredRealization.compact_factors F c hc σ

/-- A finite family of actual singular simplices factors through one common stage. -/
theorem filtered_finite_simplices_factor {ι : Type u} [Finite ι]
    (n : SimplexCategory) (σ : ι → SingularSimplex |c.pt| n) :
    ∃ j, ∃ τ : ι → SingularSimplex |F.obj j| n,
      ∀ i, (SSet.toTop.map (c.ι.app j)).hom.comp (τ i) = σ i := by
  obtain ⟨j, g, hg⟩ := Topology.FilteredRealization.compact_factors F c hc (ContinuousMap.sigma σ)
  let inc (i : ι) :=
    ContinuousMap.sigmaMk (X := fun _ : ι ↦ StdSimplex ℝ (Fin (n.len + 1))) i
  refine ⟨j, fun i ↦ g.comp (inc i), fun i ↦ ?_⟩
  exact congrArg (fun t ↦ t.comp (inc i)) hg

/-- A finite collection of whole simplex coefficient summands lifts together
through one original stage, with its actual pushforward as comparison. -/
theorem filtered_finite_summands_factor (A : System.{u, u} |c.pt|)
    {ι : Type u} [Finite ι] (n : SimplexCategory) (σ : ι → SingularSimplex |c.pt| n) :
    ∃ j, ∃ l : (∐ fun i ↦ simplexFiber A (σ i)) ⟶
      chainModule (pullback (SSet.toTop.map (c.ι.app j)).hom A) n,
      l ≫ pushforwardModuleMap (SSet.toTop.map (c.ι.app j)).hom A n =
        Sigma.desc (fun i ↦ chainInclusion A (σ i)) := by
  obtain ⟨j, τ, hτ⟩ := filtered_finite_simplices_factor F c hc n σ
  refine ⟨j, Sigma.desc (fun i ↦
    eqToHom (congrArg (simplexFiber A) (hτ i).symm) ≫
      chainInclusion (pullback (SSet.toTop.map (c.ι.app j)).hom A) (τ i)), ?_⟩
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
    Category.assoc, chainInclusion_pushforwardModuleMap]
  exact chainInclusion_congr A (hτ i).symm

/-- Two actual simplices equal in the colimit become equal at a later stage. -/
theorem filtered_simplex_eq_eventually (n : SimplexCategory) (j : J)
    (σ τ : SingularSimplex |F.obj j| n)
    (h : (SSet.toTop.map (c.ι.app j)).hom.comp σ =
      (SSet.toTop.map (c.ι.app j)).hom.comp τ) :
    ∃ k, ∃ a : j ⟶ k, (SSet.toTop.map (F.map a)).hom.comp σ =
      (SSet.toTop.map (F.map a)).hom.comp τ :=
  Topology.FilteredRealization.compact_eq_eventually F c hc j σ τ h

/-- Maps out of actual local chains are determined by their composites with
all original stage pushforwards. Coefficients are pulled back from the target. -/
theorem filtered_chainModule_hom_ext (A : System.{u, u} |c.pt|) (n : SimplexCategory)
    {V : ModuleCat.{u} ℤ} (p q : chainModule A n ⟶ V)
    (h : ∀ j, pushforwardModuleMap (SSet.toTop.map (c.ι.app j)).hom A n ≫ p =
      pushforwardModuleMap (SSet.toTop.map (c.ι.app j)).hom A n ≫ q) : p = q := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion A σ ≫ p = chainInclusion A σ ≫ q
  obtain ⟨j, τ, rfl⟩ := filtered_simplex_factors F c hc n σ
  rw [← chainInclusion_pushforwardModuleMap, Category.assoc, Category.assoc, h j]

/-- The map from all stage chain modules uses the original spatial pushforwards. -/
def filteredStageChainMap (A : System.{u, u} |c.pt|) (n : SimplexCategory) :
    (∐ fun j ↦ chainModule (pullback (SSet.toTop.map (c.ι.app j)).hom A) n) ⟶
      chainModule A n :=
  Sigma.desc fun j ↦ pushforwardModuleMap (SSet.toTop.map (c.ι.app j)).hom A n

/-- The original stage chain maps jointly generate the full local chain module. -/
theorem filteredStageChainMap_epi (A : System.{u, u} |c.pt|) (n : SimplexCategory) :
    Epi (filteredStageChainMap F c A n) where
  left_cancellation p q h := by
    apply filtered_chainModule_hom_ext F c hc A n p q
    intro j
    have hj := congrArg (fun t ↦ Sigma.ι
      (fun j ↦ chainModule (pullback (SSet.toTop.map (c.ι.app j)).hom A) n) j ≫ t) h
    simpa only [filteredStageChainMap, Sigma.ι_comp_desc_assoc] using hj

/-- Every local chain is an actual image of a finite-support sum of stage chains. -/
theorem filteredStageChainMap_surjective (A : System.{u, u} |c.pt|)
    (n : SimplexCategory) : Function.Surjective (filteredStageChainMap F c A n) :=
  (ModuleCat.epi_iff_surjective _).mp (filteredStageChainMap_epi F c hc A n)

/-- Original spatial chain maps jointly determine maps out of the full complex. -/
theorem filtered_chainComplex_hom_ext (A : System.{u, u} |c.pt|)
    {K : ChainComplex (ModuleCat.{u} ℤ) ℕ} (p q : singularChainComplex A ⟶ K)
    (h : ∀ j, pushforwardChainMap (SSet.toTop.map (c.ι.app j)).hom A ≫ p =
      pushforwardChainMap (SSet.toTop.map (c.ι.app j)).hom A ≫ q) : p = q := by
  ext n : 1
  apply filtered_chainModule_hom_ext F c hc A ⦋n⦌ (p.f n) (q.f n)
  intro j
  exact congrArg (fun t ↦ t.f n) (h j)

end FundamentalGroupoid.LocalCoefficients
