/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SmallChainRefinement
public import Colib.Topology.LocalCoefficients.RelativeChains

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SubspaceChains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.


# Actual subspace chains as one-set small chains

The original singular chains of a subspace with the restricted local system
are isomorphic to the one-set small-chain complex in the ambient space.
The isomorphism retains the original simplex and coefficient, and its
composite with the small-chain inclusion is the actual spatial chain map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- A single subset, regarded as a one-member family. -/
def singletonCover (U : Set X) : Unit → Set X := fun _ ↦ U

@[simp]
theorem isCoverSmall_singletonCover (U : Set X) {n : SimplexCategory}
    (σ : SingularSimplex X n) :
    IsCoverSmall (singletonCover U) σ ↔ Set.range σ ⊆ U := by
  simp [IsCoverSmall, singletonCover]

/-- A subspace simplex viewed in the ambient space remains in that subspace. -/
def subspaceSmallSimplex (U : Set X) {n : SimplexCategory}
    (σ : SingularSimplex U n) : CoverSmallSimplex (singletonCover U) n :=
  ⟨(subspaceInclusion U).comp σ, (isCoverSmall_singletonCover U _).mpr
    (by rintro _ ⟨x, rfl⟩; exact (σ x).property)⟩

/-- An actual small simplex, with codomain restricted to the original subset. -/
def smallSubspaceSimplex (U : Set X) {n : SimplexCategory}
    (σ : CoverSmallSimplex (singletonCover U) n) : SingularSimplex U n :=
  ⟨fun x ↦ ⟨σ.val x, (isCoverSmall_singletonCover U σ.val).mp σ.property ⟨x, rfl⟩⟩,
    σ.val.continuous.subtype_mk _⟩

@[simp]
theorem subspaceSmallSimplex_smallSubspaceSimplex (U : Set X) {n : SimplexCategory}
    (σ : CoverSmallSimplex (singletonCover U) n) :
    subspaceSmallSimplex U (smallSubspaceSimplex U σ) = σ := by
  apply Subtype.ext
  ext x
  rfl

@[simp]
theorem smallSubspaceSimplex_subspaceSmallSimplex (U : Set X) {n : SimplexCategory}
    (σ : SingularSimplex U n) :
    smallSubspaceSimplex U (subspaceSmallSimplex U σ) = σ := by
  ext x
  rfl

variable (U : Set X) (A : System.{u, u} X)

/-- The original subspace-simplex summands inside the one-set small chains. -/
def subspaceSmallModuleMap (n : SimplexCategory) :
    chainModule (pullback (subspaceInclusion U) A) n ⟶
      smallChainModule (singletonCover U) A n :=
  Sigma.desc fun σ ↦ smallChainInclusion (singletonCover U) A (subspaceSmallSimplex U σ)

/-- Restriction of each actual small simplex gives the inverse on chain modules. -/
def smallSubspaceModuleMap (n : SimplexCategory) :
    smallChainModule (singletonCover U) A n ⟶
      chainModule (pullback (subspaceInclusion U) A) n :=
  Sigma.desc fun σ ↦ chainInclusion (pullback (subspaceInclusion U) A)
    (smallSubspaceSimplex U σ)

@[reassoc (attr := simp)]
theorem subspaceSmallModuleMap_inclusion (n : SimplexCategory) :
    subspaceSmallModuleMap U A n ≫ smallModuleInclusion (singletonCover U) A n =
      pushforwardModuleMap (subspaceInclusion U) A n := by
  apply Sigma.hom_ext
  intro σ
  simp [subspaceSmallModuleMap, smallModuleInclusion, pushforwardModuleMap,
    smallChainInclusion, chainInclusion, subspaceSmallSimplex]

/-- The actual subspace and one-set small chain modules are isomorphic. -/
def subspaceSmallModuleIso (n : SimplexCategory) :
    chainModule (pullback (subspaceInclusion U) A) n ≅
      smallChainModule (singletonCover U) A n where
  hom := subspaceSmallModuleMap U A n
  inv := smallSubspaceModuleMap U A n
  hom_inv_id := by
    apply Sigma.hom_ext
    intro σ
    simp [subspaceSmallModuleMap, smallSubspaceModuleMap, chainInclusion,
      smallChainInclusion, chainModule]
    rfl
  inv_hom_id := by
    apply Sigma.hom_ext
    intro σ
    simp [subspaceSmallModuleMap, smallSubspaceModuleMap, chainInclusion,
      smallChainInclusion, smallChainModule]
    rfl

/-- The subspace comparison commutes with actual local coefficient transport. -/
@[reassoc]
theorem subspaceSmallModuleMap_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    chainMap (pullback (subspaceInclusion U) A) α ≫ subspaceSmallModuleMap U A m =
      subspaceSmallModuleMap U A n ≫ smallChainMap (singletonCover U) A α := by
  apply Sigma.hom_ext
  intro σ
  simp [chainMap, subspaceSmallModuleMap, smallChainMap, chainInclusion, smallChainInclusion]
  rfl

/-- A genuine simplicial isomorphism from subspace chains to one-set small chains. -/
def subspaceSmallSimplicialIso : simplicialModule (pullback (subspaceInclusion U) A) ≅
    smallSimplicialModule (singletonCover U) A :=
  NatIso.ofComponents (fun n ↦ subspaceSmallModuleIso U A n.unop)
    (fun α ↦ subspaceSmallModuleMap_naturality U A α.unop)

/-- The actual twisted chain complex of a subspace, without changing coefficients. -/
def subspaceSmallChainIso : singularChainComplex (pullback (subspaceInclusion U) A) ≅
    smallChainComplex (singletonCover U) A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (subspaceSmallSimplicialIso U A)

/-- The chain comparison retains the original spatial chain map. -/
@[reassoc (attr := simp)]
theorem subspaceSmallChainIso_hom_inclusion :
    (subspaceSmallChainIso U A).hom ≫ smallChainComplexInclusion (singletonCover U) A =
      pushforwardChainMap (subspaceInclusion U) A := by
  ext n : 1
  exact subspaceSmallModuleMap_inclusion U A ⦋n⦌


end FundamentalGroupoid.LocalCoefficients
