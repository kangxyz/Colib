/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.TwoSidedBar.Fibers
public import Colib.CategoryTheory.TheoremB.ReplacementWeakVertex
public import Colib.Topology.HomotopyFiber.CartesianTransport

/-!
# Zero-row fiber comparison for the two-sided bar

The vertex and zero-diagonal inclusions compare the indicated strict and homotopy fibers under the
stated transition hypotheses.


Implementation provenance:
`Quillen/Topology/Realization/TwoSidedBar/ZeroFiber.lean`
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

/-- Include the original zero row using the constant zero-ordinal chain. -/
def barZeroInclusion (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    H.obj (op ⦋0⦌) ⟶ diagonalSSet (bar H) where
  app p := ↾fun x ↦ ⟨(Functor.const (Fin (p.unop.len + 1))).obj
    (AsSmall.up.obj (op ⦋0⦌)), x, ULift.up (SimplexCategory.const p.unop ⦋0⦌ 0)⟩
  naturality p q α := by
    ext x : 3
    change (⟨(Functor.const (Fin (q.unop.len + 1))).obj (AsSmall.up.obj (op ⦋0⦌)), ((H.obj (op
      ⦋0⦌)).map α x,
      ULift.up (SimplexCategory.const q.unop ⦋0⦌ 0))⟩ : (diagonalSSet (bar H)).obj q) =
      ⟨(Functor.const (Fin (q.unop.len + 1))).obj (AsSmall.up.obj (op ⦋0⦌)), ((H.obj (op ⦋0⦌)).map α
        ((H.map (𝟙 (op ⦋0⦌))).app p x),
        ULift.up (α.unop ≫ SimplexCategory.const p.unop ⦋0⦌ 0))⟩
    rw [H.map_id]
    apply congrArg (Sigma.mk _)
    refine Prod.ext rfl ?_
    apply ULift.ext
    exact SimplexCategory.isTerminalZero.hom_ext _ _

@[reassoc] theorem barZeroInclusion_drop (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    barZeroInclusion H ≫ dropMap H =
      replacementVertexInclusion (liftedDiagram H) (AsSmall.up.obj (op ⦋0⦌)) := rfl

@[reassoc] theorem barZeroInclusion_naturality
    {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J) :
    η.app (op ⦋0⦌) ≫ barZeroInclusion J = barZeroInclusion H ≫ barMap η := rfl

@[simp] theorem barZeroInclusion_vertex (H : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (x : (H.obj (op ⦋0⦌)) _⦋0⦌) :
    (barZeroInclusion H).app (op ⦋0⦌) x = vertex H x := by
  apply congrArg (Sigma.mk _)
  refine Prod.ext rfl ?_
  apply ULift.ext
  exact SimplexCategory.isTerminalZero.hom_ext _ _

/-- A constant-row section evaluates to its original diagonal inclusion. -/
@[reassoc] theorem barZeroInclusion_evaluation_section
    {F : SSet.{u}} {H : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (σ : (Functor.const SimplexCategoryᵒᵖ).obj F ⟶ H) :
    σ.app (op ⦋0⦌) ≫ barZeroInclusion H ≫ evaluationMap H =
      (diagonalConstantIso F).inv ≫ diagonalMap σ := by
  ext p x : 4
  change (H.map (_ ≫ _)).app p ((σ.app (op ⦋0⦌)).app p x) = (σ.app p).app p x
  change (H.map (SimplexCategory.const p.unop ⦋0⦌ 0).op).app p
    ((σ.app (op ⦋0⦌)).app p x) = (σ.app p).app p x
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (σ.naturality (SimplexCategory.const p.unop ⦋0⦌ 0).op) p) x
  exact h.symm

variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)

/-- The exact square from the zero row to the original bar. -/
theorem realizedBarZeroSquare :
    (SSet.toTop.map (barZeroInclusion J)).hom.comp
      (SSet.toTop.map (η.app (op ⦋0⦌))).hom =
    (SSet.toTop.map (barMap η)).hom.comp (SSet.toTop.map (barZeroInclusion H)).hom := by
  simpa only [Functor.map_comp, TopCat.hom_comp] using
    congrArg (fun f ↦ (SSet.toTop.map f).hom) (barZeroInclusion_naturality η)

/-- The induced map retains the original zero-row source and its complete path. -/
def barZeroFiberMap (b : |J.obj (op ⦋0⦌)|) :
    C(HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b,
      HomotopyFiber (SSet.toTop.map (barMap η)).hom
        (SSet.toTop.map (barZeroInclusion J) b)) :=
  HomotopyFiber.map (SSet.toTop.map (barZeroInclusion H)).hom
    (SSet.toTop.map (barZeroInclusion J)).hom (realizedBarZeroSquare η) b

@[simp] theorem barZeroFiberMap_source (b : |J.obj (op ⦋0⦌)|)
    (z : HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b) :
    (barZeroFiberMap η b z).1.1 = SSet.toTop.map (barZeroInclusion H) z.1.1 := rfl

@[simp] theorem barZeroFiberMap_path (b : |J.obj (op ⦋0⦌)|)
    (z : HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b) :
    (barZeroFiberMap η b z).1.2 = (SSet.toTop.map (barZeroInclusion J)).hom.comp z.1.2 := rfl

/-- The canonical bar-zero fiber map is weak from the actual transition squares. -/
theorem barZeroFiberMap_isWeakHomotopyEquivalence
    (h : CategoryTheory.TheoremB.Skeletal.TransitionWeakCartesian
      (Functor.whiskerLeft indexProjection η)) (b : |J.obj (op ⦋0⦌)|) :
    IsWeakHomotopyEquivalence (barZeroFiberMap η b) := by
  have hc :=
    CategoryTheory.TheoremB.Skeletal.replacementVertexComparison_isWeakHomotopyEquivalence
    (Functor.whiskerLeft indexProjection η) h (AsSmall.up.obj (op ⦋0⦌))
  let u := (SSet.toTop.map (dropMap H)).hom.comp (SSet.toTop.map (barZeroInclusion H)).hom
  let v := (SSet.toTop.map (dropMap J)).hom.comp (SSet.toTop.map (barZeroInclusion J)).hom
  have hu : (SSet.toTop.map (replacementVertexInclusion (liftedDiagram H)
      (AsSmall.up.obj (op ⦋0⦌)))).hom = u := by
    change _ = (SSet.toTop.map (barZeroInclusion H) ≫ SSet.toTop.map (dropMap H)).hom
    rw [← Functor.map_comp, barZeroInclusion_drop]
  have hv : (SSet.toTop.map (replacementVertexInclusion (liftedDiagram J)
      (AsSmall.up.obj (op ⦋0⦌)))).hom = v := by
    change _ = (SSet.toTop.map (barZeroInclusion J) ≫ SSet.toTop.map (dropMap J)).hom
    rw [← Functor.map_comp, barZeroInclusion_drop]
  have sq : v.comp (SSet.toTop.map (η.app (op ⦋0⦌))).hom =
      (SSet.toTop.map (replacementMap η)).hom.comp u := by
    rw [← hu, ← hv]
    exact (CategoryTheory.TheoremB.Skeletal.replacementVertex_square
      (Functor.whiskerLeft indexProjection η) (AsSmall.up.obj (op ⦋0⦌))).symm
  have hc' : Topology.HomotopyPullback.WeakCartesian
      (SSet.toTop.map (η.app (op ⦋0⦌))).hom
      (SSet.toTop.map (replacementMap η)).hom u v sq.symm :=
    Topology.HomotopyPullback.WeakCartesian.congr hc rfl rfl hu hv
  have he' : IsWeakHomotopyEquivalence
      ((dropFiberMap η (SSet.toTop.map (barZeroInclusion J) b)).comp
        (barZeroFiberMap η b)) :=
    HomotopyFiber.map_isWeakHomotopyEquivalence_of_comparison u v sq hc' b
  exact he'.of_comp_right (dropFiberMap_isWeakHomotopyEquivalence η _)

/-- The zero-row diagonal map is the literal evaluation of its constant bar chain. -/
def zeroDiagonalInclusion (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    H.obj (op ⦋0⦌) ⟶ diagonalSSet H := barZeroInclusion H ≫ evaluationMap H

/-- The zero-row diagonal map commutes with the original coefficient transformation. -/
theorem realizedZeroDiagonalSquare :
    (SSet.toTop.map (zeroDiagonalInclusion J)).hom.comp
      (SSet.toTop.map (η.app (op ⦋0⦌))).hom =
    (SSet.toTop.map (diagonalMap η)).hom.comp
      (SSet.toTop.map (zeroDiagonalInclusion H)).hom := by
  have h : η.app (op ⦋0⦌) ≫ zeroDiagonalInclusion J =
      zeroDiagonalInclusion H ≫ diagonalMap η := by
    rw [zeroDiagonalInclusion, zeroDiagonalInclusion,
      ← Category.assoc, barZeroInclusion_naturality, Category.assoc,
      barMap, evaluationMap_naturality, Category.assoc]
  simpa only [Functor.map_comp, TopCat.hom_comp] using
    congrArg (fun f ↦ (SSet.toTop.map f).hom) h

/-- The original zero-row-to-diagonal fiber map, including its entire path. -/
def zeroDiagonalFiberMap (b : |J.obj (op ⦋0⦌)|) :
    C(HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b,
      HomotopyFiber (SSet.toTop.map (diagonalMap η)).hom
        (SSet.toTop.map (evaluationMap J) (SSet.toTop.map (barZeroInclusion J) b))) :=
  (evaluationFiberMap η (SSet.toTop.map (barZeroInclusion J) b)).comp
    (barZeroFiberMap η b)

@[simp] theorem zeroDiagonalFiberMap_source (b : |J.obj (op ⦋0⦌)|)
    (z : HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b) :
    (zeroDiagonalFiberMap η b z).1.1 = SSet.toTop.map (zeroDiagonalInclusion H) z.1.1 := by
  rw [zeroDiagonalInclusion, Functor.map_comp]
  rfl

/-- The complete path is postcomposed; no interval is shortened or padded. -/
@[simp] theorem zeroDiagonalFiberMap_path (b : |J.obj (op ⦋0⦌)|)
    (z : HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b) :
    (zeroDiagonalFiberMap η b z).1.2 =
      (SSet.toTop.map (zeroDiagonalInclusion J)).hom.comp z.1.2 := by
  rw [zeroDiagonalInclusion, Functor.map_comp]
  rfl

/-- Evaluation and the proved bar-zero comparison give the actual diagonal fiber map. -/
theorem zeroDiagonalFiberMap_isWeakHomotopyEquivalence
    (h : CategoryTheory.TheoremB.Skeletal.TransitionWeakCartesian
      (Functor.whiskerLeft indexProjection η)) (b : |J.obj (op ⦋0⦌)|) :
    IsWeakHomotopyEquivalence (zeroDiagonalFiberMap η b) :=
  (evaluationFiberMap_isWeakHomotopyEquivalence η _).comp
    (barZeroFiberMap_isWeakHomotopyEquivalence η h b)

@[simp] theorem zeroDiagonalInclusion_vertex
    (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (x : (H.obj (op ⦋0⦌)) _⦋0⦌) :
    (zeroDiagonalInclusion H).app (op ⦋0⦌) x = x := by
  change (evaluationMap H).app _ ((barZeroInclusion H).app _ x) = x
  rw [barZeroInclusion_vertex, evaluationMap_vertex]

theorem zeroDiagonalInclusion_realizationPoint
    (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (x : (H.obj (op ⦋0⦌)) _⦋0⦌) :
    SSet.toTop.map (zeroDiagonalInclusion H) (realizationPoint x) = realizationPoint (X :=
      diagonalSSet H) x := by
  rw [realizationPoint_naturality, zeroDiagonalInclusion_vertex]

/-- Evaluation of the actual realized zero-row chain retains the prescribed point. -/
theorem evaluation_barZero_realizationPoint
    (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (x : (H.obj (op ⦋0⦌)) _⦋0⦌) :
    SSet.toTop.map (evaluationMap H)
      (SSet.toTop.map (barZeroInclusion H) (realizationPoint x)) =
        realizationPoint (X := diagonalSSet H) x := by
  rw [realizationPoint_naturality, barZeroInclusion_vertex, evaluationMap_realizationPoint]

end SSet.TwoSidedBar

end
