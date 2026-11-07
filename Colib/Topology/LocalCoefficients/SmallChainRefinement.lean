/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SmallChains

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SmallChainRefinement.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Refinement of actual small-chain complexes

A refinement sends each original small-simplex summand to the identical
summand in a larger small-chain complex. All coefficient transports and
differentials remain those of the original local system. The construction
requires only inclusion of the predicates on actual singular simplices.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u v w

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {κ : Type w}
variable (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X)

/-- The original summand inclusion for any refinement of small simplices. -/
def smallModuleRefinement
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ) (n : SimplexCategory) :
    smallChainModule U A n ⟶ smallChainModule V A n :=
  Sigma.desc fun σ ↦ smallChainInclusion V A ⟨σ.val, h σ.property⟩

@[reassoc (attr := simp)]
theorem smallChainInclusion_refinement
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ)
    {n : SimplexCategory} (σ : CoverSmallSimplex U n) :
    smallChainInclusion U A σ ≫ smallModuleRefinement U V A h n =
      smallChainInclusion V A ⟨σ.val, h σ.property⟩ :=
  Sigma.ι_desc _ _

@[reassoc (attr := simp)]
theorem smallModuleRefinement_inclusion
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ) (n : SimplexCategory) :
    smallModuleRefinement U V A h n ≫ smallModuleInclusion V A n =
      smallModuleInclusion U A n := by
  apply Sigma.hom_ext
  intro σ
  change smallChainInclusion U A σ ≫ _ = smallChainInclusion U A σ ≫ _
  simp

/-- Refinement commutes with the genuine transported restriction maps. -/
@[reassoc]
theorem smallModuleRefinement_naturality
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ)
    {m n : SimplexCategory} (α : m ⟶ n) :
    smallChainMap U A α ≫ smallModuleRefinement U V A h m =
      smallModuleRefinement U V A h n ≫ smallChainMap V A α := by
  apply (cancel_mono (smallModuleInclusion V A m)).mp
  simp only [Category.assoc, smallModuleRefinement_inclusion,
    smallChainMap_inclusion, smallModuleRefinement_inclusion_assoc]

/-- Actual simplicial refinement of small chains. -/
def smallSimplicialRefinement
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ) :
    smallSimplicialModule U A ⟶ smallSimplicialModule V A where
  app n := smallModuleRefinement U V A h n.unop
  naturality _ _ α := smallModuleRefinement_naturality U V A h α.unop

/-- Actual chain refinement of small chains. -/
def smallChainRefinement
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ) :
    smallChainComplex U A ⟶ smallChainComplex V A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (smallSimplicialRefinement U V A h)

@[simp]
theorem smallChainRefinement_f
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ) (n : ℕ) :
    (smallChainRefinement U V A h).f n = smallModuleRefinement U V A h ⦋n⦌ := rfl

@[reassoc (attr := simp)]
theorem smallChainRefinement_inclusion
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ) :
    smallChainRefinement U V A h ≫ smallChainComplexInclusion V A =
      smallChainComplexInclusion U A := by
  ext n : 1
  exact smallModuleRefinement_inclusion U V A h ⦋n⦌

instance smallModuleRefinement_mono
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ) (n : SimplexCategory) :
    Mono (smallModuleRefinement U V A h n) :=
  mono_of_mono_fac (smallModuleRefinement_inclusion U V A h n)

instance smallChainRefinement_mono
    (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall V σ) :
    Mono (smallChainRefinement U V A h) :=
  mono_of_mono_fac (smallChainRefinement_inclusion U V A h)

end FundamentalGroupoid.LocalCoefficients
