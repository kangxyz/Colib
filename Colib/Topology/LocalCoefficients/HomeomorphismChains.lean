/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Functoriality

/-!
Adapted from `Quillen/Topology/LocalCoefficients/HomeomorphismChains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.
 # The original twisted chain map of a homeomorphism is a chain isomorphism -/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
open scoped Simplicial
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism reparametrizes the actual singular simplex indexing sets. -/
def homeomorphismSimplexEquiv (e : X ≃ₜ Y) (n : SimplexCategory) :
    SingularSimplex X n ≃ SingularSimplex Y n where
  toFun σ := (toContinuousMap e).comp σ
  invFun σ := (toContinuousMap e.symm).comp σ
  left_inv σ := by ext t; exact e.symm_apply_apply (σ t)
  right_inv σ := by ext t; exact e.apply_symm_apply (σ t)

/-- The actual reindexing isomorphism on the first-vertex coefficient modules. -/
def homeomorphismChainModuleIso (e : X ≃ₜ Y) (A : System.{u, u} Y) (n : SimplexCategory) :
    chainModule (pullback (toContinuousMap e) A) n ≅ chainModule A n :=
  Sigma.whiskerEquiv (f := fun σ : SingularSimplex X n ↦
      simplexFiber (pullback (toContinuousMap e) A) σ)
    (g := fun σ : SingularSimplex Y n ↦ simplexFiber A σ)
    (homeomorphismSimplexEquiv e n) (fun _ ↦ Iso.refl _)

/-- The reindexing is exactly the original spatial module map. -/
theorem homeomorphismChainModuleIso_hom (e : X ≃ₜ Y) (A : System.{u, u} Y)
    (n : SimplexCategory) :
    (homeomorphismChainModuleIso e A n).hom = pushforwardModuleMap (toContinuousMap e) A n := by
  apply Sigma.hom_ext
  intro σ
  simp only [homeomorphismChainModuleIso, Sigma.whiskerEquiv_hom, Iso.refl_inv,
    Sigma.ι_comp_map', pushforwardModuleMap, chainInclusion, Sigma.ι_comp_desc]
  exact Category.id_comp _

/-- The original map of chain complexes induced by a homeomorphism is invertible. -/
theorem pushforwardChainMap_isIso_of_homeomorph (e : X ≃ₜ Y) (A : System.{u, u} Y) :
    IsIso (pushforwardChainMap (toContinuousMap e) A) := by
  have (n : ℕ) : IsIso ((pushforwardChainMap (toContinuousMap e) A).f n) := by
    change IsIso (pushforwardModuleMap (toContinuousMap e) A ⦋n⦌)
    rw [← homeomorphismChainModuleIso_hom]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The chain isomorphism has the specified original homeomorphism-induced map. -/
def homeomorphismChainIso (e : X ≃ₜ Y) (A : System.{u, u} Y) :
    singularChainComplex (pullback (toContinuousMap e) A) ≅ singularChainComplex A := by
  have := pushforwardChainMap_isIso_of_homeomorph e A
  exact asIso (pushforwardChainMap (toContinuousMap e) A)

end FundamentalGroupoid.LocalCoefficients
