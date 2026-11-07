/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.RelativeChains
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.Exact
public import Colib.Topology.LocalCoefficients.HomotopyQuasiIso

/-!
Adapted from `Quillen/Topology/LocalCoefficients/RelativeHomotopyEquivalence.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.

 # Vanishing of actual relative chains for homotopy-equivalent subspaces -/
@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual relative singular complex is acyclic when the original subspace
inclusion is the forward map of a homotopy equivalence. -/
theorem relativeSingularChainComplex_acyclic_of_homotopyEquiv
    (W : Set X) (A : System.{u, u} X) (e : ContinuousMap.HomotopyEquiv W X)
    (he : e.toFun = subspaceInclusion W) :
    (relativeSingularChainComplex W A).Acyclic := by
  have hq := pushforwardChainMap_quasiIso_of_homotopyEquiv e A
  rw [he] at hq
  let S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (pushforwardChainMap (subspaceInclusion W) A)
      (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  exact hS.acyclic_X₃ hq

end FundamentalGroupoid.LocalCoefficients
