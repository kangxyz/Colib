/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.EdgePath

public import Colib.Topology.Realization.TwoSidedBar.Equivalence
public import Colib.Topology.HomotopyFiber.Map
public import Colib.Topology.HomotopyFiber.WeakSquareTransport
public import Colib.Topology.HomotopyFiber.SquareEquivalence

/-!
# Homotopy fibers of the two-sided bar augmentations

The drop and evaluation augmentations induce explicit fiber maps. Their weak equivalences and
    the stronger homotopy equivalences retain their respective hypotheses.


Implementation provenance:
`Quillen/Topology/Realization/TwoSidedBar/Fibers.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA



noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
namespace SSet.TwoSidedBar
open TheoremA

/-- The diagonal of the actual coefficientwise bar map. -/
def barMap {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J) :
    diagonalSSet (bar H) ⟶ diagonalSSet (bar J) :=
  diagonalMap (map indexProjection (Functor.whiskerLeft indexProjection η))

/-- The original map of the universe-aligned simplicial replacements. -/
def replacementMap {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J) :
    replacementDiagonal (liftedDiagram H) ⟶ replacementDiagonal (liftedDiagram J) :=
  diagonalMap (simplicialReplacementMap (Functor.whiskerLeft indexProjection η))

/-- The actual first augmentation at diagonal level. -/
def dropMap (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalSSet (bar H) ⟶ replacementDiagonal (liftedDiagram H) :=
  diagonalMap (drop indexProjection (liftedDiagram H))

variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)

/-- The complete drop square commutes in the actual simplicial category. -/
theorem dropMap_naturality :
    barMap η ≫ dropMap J = dropMap H ≫ replacementMap η :=
  congrArg diagonalMap (drop_naturality indexProjection (Functor.whiskerLeft indexProjection η))

/-- The actual realized drop square, in the orientation of the fiber-map API. -/
theorem realizedDropSquare :
    (SSet.toTop.map (dropMap J)).hom.comp (SSet.toTop.map (barMap η)).hom =
      (SSet.toTop.map (replacementMap η)).hom.comp (SSet.toTop.map (dropMap H)).hom := by
  simpa only [Functor.map_comp, TopCat.hom_comp] using
    congrArg (fun f ↦ (SSet.toTop.map f).hom) (dropMap_naturality η)

/-- The actual realized evaluation square, retaining the original diagonal map. -/
theorem realizedEvaluationSquare :
    (SSet.toTop.map (evaluationMap J)).hom.comp (SSet.toTop.map (barMap η)).hom =
      (SSet.toTop.map (diagonalMap η)).hom.comp (SSet.toTop.map (evaluationMap H)).hom := by
  have h : barMap η ≫ evaluationMap J = evaluationMap H ≫ diagonalMap η :=
    evaluationMap_naturality η
  simpa only [Functor.map_comp, TopCat.hom_comp] using
    congrArg (fun f ↦ (SSet.toTop.map f).hom) h

/-- The literal drop augmentation on original homotopy fibers. -/
def dropFiberMap (y : |diagonalSSet (bar J)|) :
    C(HomotopyFiber (SSet.toTop.map (barMap η)).hom y,
      HomotopyFiber (SSet.toTop.map (replacementMap η)).hom (SSet.toTop.map (dropMap J) y)) :=
  HomotopyFiber.map (SSet.toTop.map (dropMap H)).hom (SSet.toTop.map (dropMap J)).hom
    (realizedDropSquare η) y

/-- The literal evaluation augmentation on original homotopy fibers. -/
def evaluationFiberMap (y : |diagonalSSet (bar J)|) :
    C(HomotopyFiber (SSet.toTop.map (barMap η)).hom y,
      HomotopyFiber (SSet.toTop.map (diagonalMap η)).hom (SSet.toTop.map (evaluationMap J) y)) :=
  HomotopyFiber.map (SSet.toTop.map (evaluationMap H)).hom (SSet.toTop.map (evaluationMap J)).hom
    (realizedEvaluationSquare η) y

@[simp] theorem dropFiberMap_source (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (dropFiberMap η y p).1.1 = SSet.toTop.map (dropMap H) p.1.1 := rfl

@[simp] theorem dropFiberMap_path (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (dropFiberMap η y p).1.2 = (SSet.toTop.map (dropMap J)).hom.comp p.1.2 := rfl

@[simp] theorem evaluationFiberMap_source (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (evaluationFiberMap η y p).1.1 = SSet.toTop.map (evaluationMap H) p.1.1 := rfl

@[simp] theorem evaluationFiberMap_path (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (evaluationFiberMap η y p).1.2 = (SSet.toTop.map (evaluationMap J)).hom.comp p.1.2 := rfl

/-- Coefficient maps retain the prescribed vertex at the original zero ordinal. -/
@[simp] theorem barMap_vertex (x : (diagonalSSet H) _⦋0⦌) :
    (barMap η).app (op ⦋0⦌) (vertex H x) = vertex J ((diagonalMap η).app (op ⦋0⦌) x) := rfl

/-- Realized evaluation preserves the prescribed original point exactly. -/
theorem evaluationMap_realizationPoint (x : (diagonalSSet H) _⦋0⦌) :
    SSet.toTop.map (evaluationMap H) (realizationPoint (vertex H x)) = realizationPoint x := by
  rw [realizationPoint_naturality, evaluationMap_vertex]

end SSet.TwoSidedBar

end

noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial Topology
universe u
namespace SSet.TwoSidedBar
open TheoremA
variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)

/-- The actual coordinate-dropping augmentation gives the complete weak
homotopy equivalence on original fibers, including empty-space cases. -/
theorem dropFiberMap_isWeakHomotopyEquivalence (y : |diagonalSSet (bar J)|) :
    IsWeakHomotopyEquivalence (dropFiberMap η y) :=
  HomotopyFiber.map_isWeakHomotopyEquivalence_of_equivalences
    (dropRealizationHomotopyEquiv indexProjection (liftedDiagram H))
    (dropRealizationHomotopyEquiv indexProjection (liftedDiagram J))
    (realizedDropSquare η) y

/-- The actual evaluation augmentation gives the complete weak homotopy
equivalence to the unchanged original diagonal fiber. -/
theorem evaluationFiberMap_isWeakHomotopyEquivalence (y : |diagonalSSet (bar J)|) :
    IsWeakHomotopyEquivalence (evaluationFiberMap η y) :=
  HomotopyFiber.map_isWeakHomotopyEquivalence_of_equivalences
    (evaluationRealizationHomotopyEquiv H) (evaluationRealizationHomotopyEquiv J)
    (realizedEvaluationSquare η) y

/-- Every original finite based drop map is a bijection, including n = 0. -/
theorem dropFiberMap_bijective (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (dropFiberMap η y) (x := p) rfl) :=
  (dropFiberMap_isWeakHomotopyEquivalence η y).homotopy_bijective p n

/-- Every original finite based evaluation map is a bijection, including n = 0. -/
theorem evaluationFiberMap_bijective (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (evaluationFiberMap η y) (x := p) rfl) :=
  (evaluationFiberMap_isWeakHomotopyEquivalence η y).homotopy_bijective p n

end SSet.TwoSidedBar

end

noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial Topology
universe u
namespace SSet.TwoSidedBar
open TheoremA
variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)

/-- The original drop augmentation is a genuine equivalence on actual fibers. -/
def dropFiberHomotopyEquiv (y : |diagonalSSet (bar J)|) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (SSet.toTop.map (barMap η)).hom y)
      (HomotopyFiber (SSet.toTop.map (replacementMap η)).hom (SSet.toTop.map (dropMap J) y)) :=
  HomotopyFiber.mapHomotopyEquivOfEquivalences
    (dropRealizationHomotopyEquiv indexProjection (liftedDiagram H))
    (dropRealizationHomotopyEquiv indexProjection (liftedDiagram J))
    (realizedDropSquare η) y

@[simp] theorem dropFiberHomotopyEquiv_toFun (y : |diagonalSSet (bar J)|) :
    (dropFiberHomotopyEquiv η y).toFun = dropFiberMap η y := rfl

/-- The original evaluation augmentation is a genuine equivalence to the
unchanged original diagonal fiber. -/
def evaluationFiberHomotopyEquiv (y : |diagonalSSet (bar J)|) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (SSet.toTop.map (barMap η)).hom y)
      (HomotopyFiber (SSet.toTop.map (diagonalMap η)).hom (SSet.toTop.map (evaluationMap J) y)) :=
  HomotopyFiber.mapHomotopyEquivOfEquivalences
    (evaluationRealizationHomotopyEquiv H) (evaluationRealizationHomotopyEquiv J)
    (realizedEvaluationSquare η) y

@[simp] theorem evaluationFiberHomotopyEquiv_toFun (y : |diagonalSSet (bar J)|) :
    (evaluationFiberHomotopyEquiv η y).toFun = evaluationFiberMap η y := rfl

end SSet.TwoSidedBar

end
