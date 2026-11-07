/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.CartesianRows
public import Colib.Topology.HomotopyPullback.Products

/-! The actual cartesian prism comparisons from
`Quillen/CategoryTheory/TheoremB/CartesianProducts.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Products use the native lower
path-space contraction; no skeletal or total fiber conclusion is assumed. -/
@[expose] public noncomputable section
open Topology CategoryTheory Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.TheoremB

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)
  {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]

/-- The canonical homotopy-pullback comparison of an actual replacement
row square multiplied by an arbitrary map of geometric parameter spaces. -/
def realizedCommaPrismComparison {p q : SimplexCategoryᵒᵖ}
    (α : p ⟶ q) (k : C(K, L)) :
    C(|TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p| × K,
      HomotopyPullback ((realizedCommaRowProjection F q).prodMap (ContinuousMap.id L))
        ((discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q)
          ((nerve D).map α)).prodMap k)) :=
  HomotopyPullback.comparison _ _
    ((realizedCommaRowProjection F p).prodMap (ContinuousMap.id K))
    ((SSet.toTop.map (TheoremA.replacementRowMap (TheoremA.commaNerveDiagram F) α)).hom.prodMap k)
    (ContinuousMap.ext fun x ↦ Prod.ext
      (realizedCommaRowProjection_naturality F α x.1).symm rfl)

/-- Complete geometric prism squares are homotopy cartesian under exactly
Theorem B's transition condition. In particular this applies to the
standard simplex maps used by the realization coend. -/
def realizedCommaPrismHomotopyEquiv (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (k : C(K, L)) :
    ContinuousMap.HomotopyEquiv
      (|TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p| × K)
      (HomotopyPullback ((realizedCommaRowProjection F q).prodMap (ContinuousMap.id L))
        ((discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q)
          ((nerve D).map α)).prodMap k)) :=
  ((realizedCommaRowSquareHomotopyEquiv F h α).prodCongr
    (HomotopyPullback.identityHomotopyEquiv k)).trans
      (HomotopyPullback.prodHomeomorph _ _ _ _).toHomotopyEquiv

/-- The geometric-prism equivalence has the canonical comparison,
including the prescribed simplex map and constant base path, as forward map. -/
@[simp]
theorem realizedCommaPrismHomotopyEquiv_toFun (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (k : C(K, L)) :
    (realizedCommaPrismHomotopyEquiv F h α k).toFun = realizedCommaPrismComparison F α k := by
  apply ContinuousMap.ext
  intro x
  change HomotopyPullback.prodHomeomorph _ _ _ _
    ((realizedCommaRowSquareHomotopyEquiv F h α).toFun x.1,
      (HomotopyPullback.identityHomotopyEquiv k).toFun x.2) = _
  rw [realizedCommaRowSquareHomotopyEquiv_toFun, HomotopyPullback.identityHomotopyEquiv_toFun]
  exact HomotopyPullback.prodHomeomorph_comparison _ _ _ _ _ _ _ _ _ _ x

end CategoryTheory.TheoremB
