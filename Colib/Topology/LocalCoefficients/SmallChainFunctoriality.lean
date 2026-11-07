/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SmallChainRefinement
public import Colib.Topology.LocalCoefficients.Functoriality
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SmallChainFunctoriality.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.


# Spatial functoriality of actual twisted small chains

A continuous map which sends small simplices to small simplices induces the
original spatial chain map on those subcomplexes. The source coefficients
are the genuine pullback of the target system. No coefficient trivialization
or presumed homology comparison is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u v w v' w'

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {ι : Type v} {κ : Type w}
variable (f : C(X, Y)) (U : ι → Set X) (V : κ → Set Y)
  (A : System.{u, u} Y)
  (h : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
    IsCoverSmall U σ → IsCoverSmall V (f.comp σ))

/-- The original spatial map on the actual small-simplex summands. -/
def smallPushforwardModuleMap (n : SimplexCategory) :
    smallChainModule U (pullback f A) n ⟶ smallChainModule V A n :=
  Sigma.desc fun σ ↦ smallChainInclusion V A ⟨f.comp σ.val, h σ.property⟩

@[reassoc (attr := simp)]
theorem smallChainInclusion_pushforward {n : SimplexCategory} (σ : CoverSmallSimplex U n) :
    smallChainInclusion U (pullback f A) σ ≫ smallPushforwardModuleMap f U V A h n =
      smallChainInclusion V A ⟨f.comp σ.val, h σ.property⟩ :=
  Sigma.ι_desc _ _

/-- Small spatial maps retain the original ambient pushforward. -/
@[reassoc (attr := simp)]
theorem smallPushforwardModuleMap_inclusion (n : SimplexCategory) :
    smallPushforwardModuleMap f U V A h n ≫ smallModuleInclusion V A n =
      smallModuleInclusion U (pullback f A) n ≫ pushforwardModuleMap f A n := by
  apply Sigma.hom_ext
  intro σ
  simp [smallPushforwardModuleMap, smallModuleInclusion, pushforwardModuleMap,
    smallChainInclusion, chainInclusion]

/-- Spatial small-chain maps commute with the original coefficient transports. -/
@[reassoc]
theorem smallPushforwardModuleMap_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    smallChainMap U (pullback f A) α ≫ smallPushforwardModuleMap f U V A h m =
      smallPushforwardModuleMap f U V A h n ≫ smallChainMap V A α := by
  apply Sigma.hom_ext
  intro σ
  simp [smallChainMap, smallPushforwardModuleMap, smallChainInclusion]
  rfl

/-- The actual spatial map on small simplicial modules. -/
def smallPushforwardSimplicialMap :
    smallSimplicialModule U (pullback f A) ⟶ smallSimplicialModule V A where
  app n := smallPushforwardModuleMap f U V A h n.unop
  naturality _ _ α := smallPushforwardModuleMap_naturality f U V A h α.unop

/-- The actual spatial map of small chain complexes. -/
def smallPushforwardChainMap : smallChainComplex U (pullback f A) ⟶ smallChainComplex V A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (smallPushforwardSimplicialMap f U V A h)

@[simp]
theorem smallPushforwardChainMap_f (n : ℕ) :
    (smallPushforwardChainMap f U V A h).f n = smallPushforwardModuleMap f U V A h ⦋n⦌ := rfl

/-- The square with both original small-chain inclusions commutes exactly. -/
@[reassoc (attr := simp)]
theorem smallPushforwardChainMap_inclusion :
    smallPushforwardChainMap f U V A h ≫ smallChainComplexInclusion V A =
      smallChainComplexInclusion U (pullback f A) ≫ pushforwardChainMap f A := by
  ext n : 1
  exact smallPushforwardModuleMap_inclusion f U V A h ⦋n⦌

variable {ι' : Type v'} {κ' : Type w'}

/-- Refinement commutes with original spatial small-chain maps. -/
@[reassoc]
theorem smallPushforwardChainMap_refinement (U' : ι' → Set X) (V' : κ' → Set Y)
    (h' : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U' σ → IsCoverSmall V' (f.comp σ))
    (hU : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U σ → IsCoverSmall U' σ)
    (hV : ∀ {n : SimplexCategory} {σ : SingularSimplex Y n},
      IsCoverSmall V σ → IsCoverSmall V' σ) :
    smallChainRefinement U U' (pullback f A) hU ≫ smallPushforwardChainMap f U' V' A h' =
      smallPushforwardChainMap f U V A h ≫ smallChainRefinement V V' A hV := by
  ext n : 1
  apply Sigma.hom_ext
  intro σ
  simp [smallChainRefinement, smallSimplicialRefinement, smallModuleRefinement,
    smallPushforwardChainMap, smallPushforwardSimplicialMap, smallPushforwardModuleMap,
    smallChainInclusion]

/-- A pointwise map between cover members sends actual small simplices to small simplices. -/
theorem IsCoverSmall.map {f : C(X, Y)} {U : ι → Set X} {V : κ → Set Y}
    (index : ι → κ) (h : ∀ i, Set.MapsTo f (U i) (V (index i)))
    {n : SimplexCategory} {σ : SingularSimplex X n} (hσ : IsCoverSmall U σ) :
    IsCoverSmall V (f.comp σ) := by
  obtain ⟨i, hi⟩ := hσ
  exact ⟨index i, by rintro _ ⟨x, rfl⟩; exact h i (hi ⟨x, rfl⟩)⟩

/-- Equal small-simplex predicates give an isomorphism retaining every summand. -/
def smallChainIsoOfPredicateIff {Z : Type u} [TopologicalSpace Z]
    {α : Type v} {β : Type w} (W : α → Set Z) (W' : β → Set Z)
    (B : System.{u, u} Z)
    (h : ∀ {n : SimplexCategory} (σ : SingularSimplex Z n),
      IsCoverSmall W σ ↔ IsCoverSmall W' σ) :
    smallChainComplex W B ≅ smallChainComplex W' B where
  hom := smallChainRefinement W W' B (fun hσ ↦ (h _).mp hσ)
  inv := smallChainRefinement W' W B (fun hσ ↦ (h _).mpr hσ)
  hom_inv_id := by
    ext n : 1
    apply Sigma.hom_ext
    intro σ
    simp [smallChainRefinement, smallSimplicialRefinement, smallModuleRefinement,
      smallChainInclusion, smallChainComplex, smallSimplicialModule, smallChainModule]
  inv_hom_id := by
    ext n : 1
    apply Sigma.hom_ext
    intro σ
    simp [smallChainRefinement, smallSimplicialRefinement, smallModuleRefinement,
      smallChainInclusion, smallChainComplex, smallSimplicialModule, smallChainModule]

/-- Reindexing equal small-simplex predicates preserves the actual spatial comparison. -/
theorem smallPushforwardChainMap_quasiIso_of_cover_iff
    (U' : ι' → Set X) (V' : κ' → Set Y)
    (h' : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
      IsCoverSmall U' σ → IsCoverSmall V' (f.comp σ))
    (hU : ∀ {n : SimplexCategory} (σ : SingularSimplex X n),
      IsCoverSmall U σ ↔ IsCoverSmall U' σ)
    (hV : ∀ {n : SimplexCategory} (σ : SingularSimplex Y n),
      IsCoverSmall V σ ↔ IsCoverSmall V' σ)
    (hf : QuasiIso (smallPushforwardChainMap f U V A h)) :
    QuasiIso (smallPushforwardChainMap f U' V' A h') := by
  let eX := smallChainIsoOfPredicateIff U U' (pullback f A) hU
  let eY := smallChainIsoOfPredicateIff V V' A hV
  have hw : eX.hom ≫ smallPushforwardChainMap f U' V' A h' =
      smallPushforwardChainMap f U V A h ≫ eY.hom :=
    smallPushforwardChainMap_refinement f U V A h U' V' h'
      (fun hσ ↦ (hU _).mp hσ) (fun hσ ↦ (hV _).mp hσ)
  have hc : QuasiIso (eX.hom ≫ smallPushforwardChainMap f U' V' A h') := by
    rw [hw]
    infer_instance
  exact (quasiIso_iff_comp_left eX.hom _).mp hc

end FundamentalGroupoid.LocalCoefficients
