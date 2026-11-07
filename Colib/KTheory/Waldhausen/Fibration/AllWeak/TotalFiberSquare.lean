/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.EdgePath

public import Colib.KTheory.Waldhausen.Fibration.AllWeak.RelativeInclusion
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.TotalFiber

/-! # The original all-weak square of total-tail fiber comparisons

The actual double-S identification and relative inclusion induce the literal
map on original homotopy fibers. It retains both the original source map and
the complete postcomposed path. Its square with the original constant-path
total comparisons commutes strictly, without assuming either global weak
fiber comparison.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AllWeak/TotalFiberSquare.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration.RelativeRows


noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.AllWeak
open RelativeRows
variable {C : Type u} [SmallCategory C]

/-- The actual original inclusion on ordinary double-S realizations. -/
def ordinaryTotalInclusionMap (W : Structure C) :
    C(|SSet.diagonalSSet (ordinarySRows (acyclicStructure (nested W)))|,
      |SSet.diagonalSSet (ordinarySRows W)|) :=
  (SSet.toTop.map (ordinaryDiagonalIso W).hom).hom

/-- It is the actual homeomorphism furnished by the proved original diagonal iso. -/
def ordinaryTotalHomeomorph (W : Structure C) :
    |SSet.diagonalSSet (ordinarySRows (acyclicStructure (nested W)))| ≃ₜ
      |SSet.diagonalSSet (ordinarySRows W)| :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (ordinaryDiagonalIso W))

@[simp] theorem ordinaryTotalHomeomorph_toContinuousMap (W : Structure C) :
    (ordinaryTotalHomeomorph W : C(
      |SSet.diagonalSSet (ordinarySRows (acyclicStructure (nested W)))|,
      |SSet.diagonalSSet (ordinarySRows W)|)) = ordinaryTotalInclusionMap W := rfl

/-- The actual double-S chosen zero is preserved by the original inclusion. -/
@[simp] theorem ordinaryTotalInclusionMap_basepoint (W : Structure C) :
    ordinaryTotalInclusionMap W (ordinaryTotalBasepoint (acyclicStructure (nested W))) =
      ordinaryTotalBasepoint W := by
  change SSet.toTop.map (ordinaryDiagonalIso W).hom
    (SSet.realizationPoint (ordinaryTotalZeroVertex (acyclicStructure (nested W)))) = _
  rw [SSet.realizationPoint_naturality]
  exact congrArg SSet.realizationPoint (ordinaryRowsInclusion_zero W ⦋0⦌ ⦋0⦌)

variable {V : Structure C} (N : NestedWeakEquivalences V)

/-- The original realized inclusion of the actual all-weak relative total. -/
def relativeTotalInclusionMap :
    C(|SSet.diagonalSSet (relativeSRows (nested (acyclicStructure N)))|,
      |SSet.diagonalSSet (relativeSRows N)|) :=
  (SSet.toTop.map (relativeInclusionTotal N)).hom

/-- The exact original realized tail square uses the exact original base homeomorphism. -/
theorem relativeTotalInclusion_tail :
    (ordinaryTotalInclusionMap (acyclicStructure N)).comp
      (totalTailMap (nested (acyclicStructure N))) =
        (totalTailMap N).comp (relativeTotalInclusionMap N) := by
  have h := congrArg SSet.diagonalMap (relativeInclusionSRows_tail N)
  have h' := congrArg (fun f ↦ (SSet.toTop.map f).hom) h
  change (SSet.toTop.map (relativeInclusionTotal N ≫ SSet.diagonalMap (tailSRows N))).hom =
    (SSet.toTop.map (SSet.diagonalMap (tailSRows (nested (acyclicStructure N))) ≫
      (ordinaryDiagonalIso (acyclicStructure N)).hom)).hom at h'
  simpa only [Functor.map_comp, TopCat.hom_comp, ordinaryTotalInclusionMap,
    totalTailMap, relativeTotalInclusionMap] using h'.symm

/-- The original map of actual fibers, with the complete original path
postcomposed by the actual ordinary double-S inclusion. -/
def relativeTailFiberMap : C(
    HomotopyFiber (totalTailMap (nested (acyclicStructure N)))
      (ordinaryTotalBasepoint (acyclicStructure (nested (acyclicStructure N)))),
    HomotopyFiber (totalTailMap N) (ordinaryTotalBasepoint (acyclicStructure N))) where
  toFun z := ⟨(relativeTotalInclusionMap N z.1.1,
    (ordinaryTotalInclusionMap (acyclicStructure N)).comp z.1.2),
    (congrArg (ordinaryTotalInclusionMap (acyclicStructure N)) z.2.1).trans
      (ContinuousMap.congr_fun (relativeTotalInclusion_tail N) z.1.1),
    (congrArg (ordinaryTotalInclusionMap (acyclicStructure N)) z.2.2).trans
      (ordinaryTotalInclusionMap_basepoint (acyclicStructure N))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact (ContinuousMap.continuous_postcomp
        (ordinaryTotalInclusionMap (acyclicStructure N))).comp (by fun_prop)

@[simp] theorem relativeTailFiberMap_source
    (z : HomotopyFiber (totalTailMap (nested (acyclicStructure N)))
      (ordinaryTotalBasepoint (acyclicStructure (nested (acyclicStructure N))))) :
    (relativeTailFiberMap N z).1.1 = relativeTotalInclusionMap N z.1.1 := rfl

@[simp] theorem relativeTailFiberMap_path
    (z : HomotopyFiber (totalTailMap (nested (acyclicStructure N)))
      (ordinaryTotalBasepoint (acyclicStructure (nested (acyclicStructure N))))) :
    (relativeTailFiberMap N z).1.2 =
      (ordinaryTotalInclusionMap (acyclicStructure N)).comp z.1.2 := rfl

/-- The original constant-path total comparisons commute strictly, including
all of their stored paths. Neither comparison is assumed weak here. -/
theorem relativeTailFiberMap_totalTailFiberComparison :
    (relativeTailFiberMap N).comp (totalTailFiberComparison (nested (acyclicStructure N))) =
      (totalTailFiberComparison N).comp (acyclicInclusionMap N) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg (fun f ↦ (SSet.toTop.map f).hom)
      (totalFiberInclusion_relativeInclusion N)
    rw [Functor.map_comp, Functor.map_comp, TopCat.hom_comp, TopCat.hom_comp] at h
    exact ContinuousMap.congr_fun h x
  · apply ContinuousMap.ext
    intro t
    exact ordinaryTotalInclusionMap_basepoint (acyclicStructure N)

/-- The original zero-source fiber point is retained, with its constant path. -/
@[simp] theorem relativeTailFiberMap_basepoint :
    relativeTailFiberMap N
      (HomotopyFiber.basepoint (totalTailMap (nested (acyclicStructure N)))
        (ordinaryTotalBasepoint (acyclicStructure (nested (acyclicStructure N))))
        (totalBasepoint (nested (acyclicStructure N)))
        (totalTailMap_basepoint (nested (acyclicStructure N)))) =
      HomotopyFiber.basepoint (totalTailMap N) (ordinaryTotalBasepoint (acyclicStructure N))
        (totalBasepoint N) (totalTailMap_basepoint N) := by
  apply Subtype.ext
  apply Prod.ext
  · exact relativeInclusionTotal_basepoint N
  · apply ContinuousMap.ext
    intro t
    exact ordinaryTotalInclusionMap_basepoint (acyclicStructure N)

end CategoryTheory.Waldhausen.Fibration.AllWeak
