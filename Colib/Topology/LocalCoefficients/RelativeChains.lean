/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.Topology.LocalCoefficients.SubspaceChains
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Relative twisted chains as the actual subspace-inclusion cokernel

The relative-chain definition from `Quillen/Topology/LocalCoefficients/SmallChainExcision.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd` belongs below excision. The original
subspace inclusion is monic by its actual degreewise simplex-restriction left inverse.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial
universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- The actual subspace inclusion is injective on each twisted chain module. -/
instance subspaceInclusion_pushforwardModuleMap_mono (U : Set X) (A : System.{u, u} X)
    (n : SimplexCategory) : Mono (pushforwardModuleMap (subspaceInclusion U) A n) :=
  mono_of_mono_fac (subspaceInclusion_projection U A n)

/-- The actual subspace inclusion is monic on the original singular complex. -/
instance subspaceInclusion_pushforwardChainMap_mono (U : Set X) (A : System.{u, u} X) :
    Mono (pushforwardChainMap (subspaceInclusion U) A) where
  right_cancellation f g h := by
    ext n : 1
    exact (cancel_mono (pushforwardModuleMap (subspaceInclusion U) A ⦋n⦌)).mp
      (congrArg (fun k ↦ k.f n) h)

/-- Relative singular chains retain the original subspace inclusion and its pullback system. -/
def relativeSingularChainComplex (U : Set X) (A : System.{u, u} X) :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  cokernel (pushforwardChainMap (subspaceInclusion U) A)

end FundamentalGroupoid.LocalCoefficients
