/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.RealizedRowFibers
public import Colib.Topology.HomotopyPullback.Basic

/-!
# Homotopy cartesian comma-replacement rows

Discrete coproduct coordinates identify the path-space pullback. Theorem B's transition hypothesis
  makes the complete replacement-row squares homotopy cartesian with their canonical forward maps.
  These are row statements; the total realization requires further results.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/CartesianRows.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual comma categories, nerves and
path-space maps are retained; no fiber-equivalence conclusion is assumed. -/
@[expose] public section


noncomputable section

open Topology CategoryTheory Opposite
open scoped Simplicial Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory

namespace TheoremB

section CoproductSquares

variable {ι κ : Type u} [TopologicalSpace ι] [DiscreteTopology ι]
  [TopologicalSpace κ] [DiscreteTopology κ]
  {X : ι → Type u} {Y : κ → Type u}
  [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]

/-- The base map of a reindexed coproduct square. -/
def discreteReindexMap (a : ι → κ) : C(ι, κ) := ⟨a, continuous_of_discreteTopology⟩

/-- The canonical comparison of a reindexed coproduct square to its actual
homotopy pullback. -/
def sigmaSquareComparison (a : ι → κ) (f : ∀ i, C(X i, Y (a i))) :
    C((Σ i, X i), HomotopyPullback (sigmaProjection Y) (discreteReindexMap a)) :=
  HomotopyPullback.comparison _ _ (sigmaProjection X)
    (sigmaReindexContinuousMap a f) rfl

/-- The path-space pullback of a coproduct projection along a discrete map
is homeomorphic to the coproduct of the selected fibers. -/
def sigmaPullbackHomeomorph (a : ι → κ) :
    (Σ i, Y (a i)) ≃ₜ HomotopyPullback (sigmaProjection Y) (discreteReindexMap a) := by
  let E : (Σ i, Y (a i)) ≃ₜ Σ i, HomotopyFiber (sigmaProjection Y) (a i) :=
    { toFun z := ⟨z.1, (sigmaProjectionFiberHomeomorph Y (a z.1)).symm z.2⟩
      invFun z := ⟨z.1, sigmaProjectionFiberHomeomorph Y (a z.1) z.2⟩
      left_inv z := by cases z; simp
      right_inv z := by cases z; simp
      continuous_toFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp
        (sigmaProjectionFiberHomeomorph Y (a i)).symm.continuous
      continuous_invFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp
        (sigmaProjectionFiberHomeomorph Y (a i)).continuous }
  exact E.trans (HomotopyPullback.sigmaFibersHomeomorph (sigmaProjection Y)
    (discreteReindexMap a))

/-- Componentwise homotopy equivalences make the entire coproduct square
homotopy cartesian. No equivalence of the index spaces is required. -/
def sigmaSquareHomotopyEquiv (a : ι → κ)
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y (a i))) :
    ContinuousMap.HomotopyEquiv (Σ i, X i)
      (HomotopyPullback (sigmaProjection Y) (discreteReindexMap a)) :=
  (ContinuousMap.sigmaHomotopyEquiv e).trans (sigmaPullbackHomeomorph a).toHomotopyEquiv

/-- The homotopy equivalence uses exactly the canonical comparison map. -/
@[simp]
theorem sigmaSquareHomotopyEquiv_toFun (a : ι → κ)
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y (a i))) :
    (sigmaSquareHomotopyEquiv a e).toFun = sigmaSquareComparison a (fun i ↦ (e i).toFun) := rfl

end CoproductSquares

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The complete topological comma-replacement square, compared with the
actual homotopy pullback of its lower and right-hand maps. -/
def commaRowSquareComparison {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    C((topologicalReplacement (TheoremA.commaNerveDiagram F)).obj p,
      HomotopyPullback (commaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α))) :=
  sigmaSquareComparison (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α)
    (fun s ↦ transitionMap F (TheoremA.firstVertexEdge α s))

/-- Theorem B's precise hypothesis makes every topological replacement
square genuinely homotopy cartesian. -/
def commaRowSquareHomotopyEquiv (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    ContinuousMap.HomotopyEquiv
      ((topologicalReplacement (TheoremA.commaNerveDiagram F)).obj p)
      (HomotopyPullback (commaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α))) :=
  sigmaSquareHomotopyEquiv (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α)
    (fun s ↦ transitionHomotopyEquiv F h (TheoremA.firstVertexEdge α s))

@[simp]
theorem commaRowSquareHomotopyEquiv_toFun (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    (commaRowSquareHomotopyEquiv F h α).toFun = commaRowSquareComparison F α := rfl

/-- The actual realized row square has its canonical constant-path map
into the actual path-space homotopy pullback. -/
def realizedCommaRowSquareComparison {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    C(|TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p|,
      HomotopyPullback (realizedCommaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α))) :=
  HomotopyPullback.comparison _ _ (realizedCommaRowProjection F p)
    (SSet.toTop.map (TheoremA.replacementRowMap (TheoremA.commaNerveDiagram F) α)).hom
    (ContinuousMap.ext fun x ↦ (realizedCommaRowProjection_naturality F α x).symm)

/-- Row coordinates transport the entire homotopy pullback, including its
path-space topology. -/
def realizedCommaRowPullbackCoordinates {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    HomotopyPullback (realizedCommaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α)) ≃ₜ
      HomotopyPullback (commaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α)) :=
  HomotopyPullback.sourceHomeomorph (commaRowProjection F q) _
    (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso (TheoremA.commaNerveDiagram F) q))

/-- The actual row comparison becomes the coproduct comparison under the
proved coordinate homeomorphisms. -/
theorem realizedCommaRowSquareComparison_coordinates {p q : SimplexCategoryᵒᵖ}
    (α : p ⟶ q) (x : |TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p|) :
    realizedCommaRowPullbackCoordinates F α (realizedCommaRowSquareComparison F α x) =
      commaRowSquareComparison F α
        ((TheoremA.replacementRowRealizationIso (TheoremA.commaNerveDiagram F) p).hom x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact ConcreteCategory.congr_hom
        (replacementRowRealizationIso_naturality (TheoremA.commaNerveDiagram F) α) x
    · rfl

/-- Under precisely Theorem B's transition hypothesis, each complete
square of the actual realized rows is homotopy cartesian. -/
def realizedCommaRowSquareHomotopyEquiv (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    ContinuousMap.HomotopyEquiv
      |TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p|
      (HomotopyPullback (realizedCommaRowProjection F q)
        (discreteReindexMap (ι := ChainSpace D p) (κ := ChainSpace D q) ((nerve D).map α))) :=
  ((TopCat.homeoOfIso
    (TheoremA.replacementRowRealizationIso (TheoremA.commaNerveDiagram F) p)).toHomotopyEquiv.trans
      (commaRowSquareHomotopyEquiv F h α)).trans
        (realizedCommaRowPullbackCoordinates F α).symm.toHomotopyEquiv

/-- The cartesian equivalence retains the canonical actual-row comparison
as its forward continuous map. -/
@[simp]
theorem realizedCommaRowSquareHomotopyEquiv_toFun (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    (realizedCommaRowSquareHomotopyEquiv F h α).toFun =
      realizedCommaRowSquareComparison F α := by
  apply ContinuousMap.ext
  intro x
  apply (realizedCommaRowPullbackCoordinates F α).injective
  change realizedCommaRowPullbackCoordinates F α
    ((realizedCommaRowPullbackCoordinates F α).symm _) = _
  rw [Homeomorph.apply_symm_apply, realizedCommaRowSquareComparison_coordinates]
  rfl

end TheoremB
end CategoryTheory

end
