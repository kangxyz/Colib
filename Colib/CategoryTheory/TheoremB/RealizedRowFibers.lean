/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.RowFibers
public import Colib.Topology.HomotopyFiber.SourceHomeomorph

/-!
# Homotopy fibers of the actual realized replacement rows

The coproduct coordinates provide homeomorphisms of the genuine path-space
fibers of realized replacement rows with the corresponding comma spaces.
Every simplex operator induces the prescribed transition under these
homeomorphisms. Consequently Theorem B's hypothesis proves homotopy
cartesianness fiberwise in each actual realized row, without replacing
realization or homotopy fibers by formal stand-ins.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/RealizedRowFibers.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual comma categories, nerves and
path-space maps are retained; no fiber-equivalence conclusion is assumed. -/
@[expose] public section


noncomputable section

open Topology CategoryTheory Opposite
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false



namespace CategoryTheory.TheoremB

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The projection from the actual realization of a comma replacement row
to its discrete space of base chains. -/
def realizedCommaRowProjection (p : SimplexCategoryᵒᵖ) :
    C(|TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p|, ChainSpace D p) :=
  (commaRowProjection F p).comp
    (TheoremA.replacementRowRealizationIso (TheoremA.commaNerveDiagram F) p).hom.hom

/-- Change to coproduct coordinates is an actual homeomorphism of homotopy fibers. -/
def realizedCommaRowFiberCoordinates (p : SimplexCategoryᵒᵖ) (s : ChainSpace D p) :
    HomotopyFiber (realizedCommaRowProjection F p) s ≃ₜ
      HomotopyFiber (commaRowProjection F p) s :=
  HomotopyFiber.sourceHomeomorph (commaRowProjection F p)
    (TopCat.homeoOfIso (TheoremA.replacementRowRealizationIso (TheoremA.commaNerveDiagram F) p)) s

/-- The actual homotopy fiber of a realized replacement row is its comma space. -/
def realizedCommaRowFiberHomeomorph (p : SimplexCategoryᵒᵖ) (s : ChainSpace D p) :
    HomotopyFiber (realizedCommaRowProjection F p) s ≃ₜ
      ClassifyingSpace (CostructuredArrow F (s.obj 0)) :=
  (realizedCommaRowFiberCoordinates F p s).trans
    (sigmaProjectionFiberHomeomorph
      (fun s : ChainSpace D p ↦ ClassifyingSpace (CostructuredArrow F (s.obj 0))) s)

/-- The inverse fiber homeomorphism includes the prescribed comma summand
into the actual realized row. -/
@[simp]
theorem realizedCommaRowFiberHomeomorph_symm_projection (p : SimplexCategoryᵒᵖ)
    (s : ChainSpace D p) (x : ClassifyingSpace (CostructuredArrow F (s.obj 0))) :
    HomotopyFiber.projection (realizedCommaRowProjection F p) s
      ((realizedCommaRowFiberHomeomorph F p s).symm x) =
      SSet.toTop.map (SSet.simplicialSigmaι
        (fun t : (nerve D).obj p ↦ (TheoremA.commaNerveDiagram F).obj (t.obj 0)) s) x :=
  SSet.realizationSigmaIso_inv_apply
    (fun t : (nerve D).obj p ↦ (TheoremA.commaNerveDiagram F).obj (t.obj 0)) s x

/-- The inverse includes the summand with the actual constant path in the
discrete base chain space. -/
@[simp]
theorem realizedCommaRowFiberHomeomorph_symm_path (p : SimplexCategoryᵒᵖ)
    (s : ChainSpace D p) (x : ClassifyingSpace (CostructuredArrow F (s.obj 0))) :
    ((realizedCommaRowFiberHomeomorph F p s).symm x).1.2 =
      ContinuousMap.const unitInterval s := rfl

/-- The projection squares for actual row realizations commute strictly. -/
theorem realizedCommaRowProjection_naturality {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    (x : |TheoremA.replacementRow (TheoremA.commaNerveDiagram F) p|) :
    (nerve D).map α (realizedCommaRowProjection F p x) =
      realizedCommaRowProjection F q
        (SSet.toTop.map (TheoremA.replacementRowMap (TheoremA.commaNerveDiagram F) α) x) := by
  have hn := ConcreteCategory.congr_hom
    (replacementRowRealizationIso_naturality (TheoremA.commaNerveDiagram F) α) x
  exact congrArg Sigma.fst hn.symm

/-- The canonical map of actual homotopy fibers induced by a simplex operator. -/
def realizedCommaRowFiberMap {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (s : ChainSpace D p) :
    C(HomotopyFiber (realizedCommaRowProjection F p) s,
      HomotopyFiber (realizedCommaRowProjection F q) ((nerve D).map α s)) :=
  HomotopyFiber.map (f₁ := realizedCommaRowProjection F p) (f₂ := realizedCommaRowProjection F q)
    (SSet.toTop.map (TheoremA.replacementRowMap (TheoremA.commaNerveDiagram F) α)).hom
    (show C(ChainSpace D p, ChainSpace D q) from
      ⟨fun s ↦ (nerve D).map α s, continuous_of_discreteTopology⟩)
    (ContinuousMap.ext (realizedCommaRowProjection_naturality F α)) s

/-- Coproduct coordinates intertwine the actual and displayed row-fiber maps. -/
theorem realizedCommaRowFiberCoordinates_naturality {p q : SimplexCategoryᵒᵖ}
    (α : p ⟶ q) (s : ChainSpace D p)
    (z : HomotopyFiber (realizedCommaRowProjection F p) s) :
    realizedCommaRowFiberCoordinates F q ((nerve D).map α s)
      (realizedCommaRowFiberMap F α s z) =
      commaRowFiberMap F α s (realizedCommaRowFiberCoordinates F p s z) := by
  apply Subtype.ext
  apply Prod.ext
  · exact ConcreteCategory.congr_hom
      (replacementRowRealizationIso_naturality (TheoremA.commaNerveDiagram F) α) z.1.1
  · rfl

/-- Under the actual row-fiber homeomorphisms, the induced map is exactly the
transition associated to the first-vertex edge of the simplex operator. -/
theorem realizedCommaRowFiberHomeomorph_naturality {p q : SimplexCategoryᵒᵖ}
    (α : p ⟶ q) (s : ChainSpace D p)
    (z : HomotopyFiber (realizedCommaRowProjection F p) s) :
    realizedCommaRowFiberHomeomorph F q ((nerve D).map α s)
      (realizedCommaRowFiberMap F α s z) =
      transitionMap F (TheoremA.firstVertexEdge α s)
        (realizedCommaRowFiberHomeomorph F p s z) := by
  change sigmaProjectionFiberHomeomorph _ _
    (realizedCommaRowFiberCoordinates F q _ (realizedCommaRowFiberMap F α s z)) = _
  rw [realizedCommaRowFiberCoordinates_naturality]
  exact sigmaFiberMap_homeomorph _ _ _ _

/-- The actual row-fiber maps are homotopy equivalences under the precise
transition hypothesis of Theorem B. -/
def realizedCommaRowFiberHomotopyEquiv (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (s : ChainSpace D p) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (realizedCommaRowProjection F p) s)
      (HomotopyFiber (realizedCommaRowProjection F q) ((nerve D).map α s)) :=
  ((realizedCommaRowFiberHomeomorph F p s).toHomotopyEquiv.trans
    (transitionHomotopyEquiv F h (TheoremA.firstVertexEdge α s))).trans
      (realizedCommaRowFiberHomeomorph F q ((nerve D).map α s)).symm.toHomotopyEquiv

/-- The equivalence has the actual simplex-induced fiber map as its forward map. -/
@[simp]
theorem realizedCommaRowFiberHomotopyEquiv_toFun (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (s : ChainSpace D p) :
    (realizedCommaRowFiberHomotopyEquiv F h α s).toFun = realizedCommaRowFiberMap F α s := by
  apply ContinuousMap.ext
  intro z
  apply (realizedCommaRowFiberHomeomorph F q ((nerve D).map α s)).injective
  change realizedCommaRowFiberHomeomorph F q ((nerve D).map α s)
    ((realizedCommaRowFiberHomeomorph F q ((nerve D).map α s)).symm _) = _
  rw [Homeomorph.apply_symm_apply, realizedCommaRowFiberHomeomorph_naturality]
  rfl

end CategoryTheory.TheoremB
