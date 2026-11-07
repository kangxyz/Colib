/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.Additivity
public import Colib.KTheory.Waldhausen.Iterated.PathObject
public import Colib.Topology.Realization.SplitFiberCartesian
public import Colib.Topology.Realization.TwoSidedBar.ZeroFiber
public import Colib.CategoryTheory.TheoremB.VertexWeakAssembly

/-!
# The original total fiber comparison at every iterated S-stage

The proved higher first/tail equivalences make the actual ordinal squares weakly cartesian.
The accepted zero-diagonal fiber theorem then proves complete weakness of the original
constant-path total fiber inclusion, including degree zero. Its identification retains both
the original source coordinate and every point of the complete fiber path.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/FiberComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps,
complete weak-equivalence statements, fiber paths and independent original universes are
  retained. -/
@[expose] public section

open CategoryTheory.TheoremA
open SSet.TwoSidedBar
open CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.Fibration.RelativeRows



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
  SSet Topology
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory
open Fibration Fibration.RelativeRows CategoryTheory.TheoremB.Skeletal

/-- Actual higher first/tail equivalences, retaining their specified forward maps. -/
def stageFirstTailRealizationEquiv (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n :
  SimplexCategory) :=
  (stageFirstTail_equivalence r W n).choose

lemma stageFirstTailRealizationEquiv_toFun (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n :
  SimplexCategory) :
    (stageFirstTailRealizationEquiv r W n).toFun = (SSet.toTop.map (stageFirstTail r W n)).hom :=
  (stageFirstTail_equivalence r W n).choose_spec

/-- The realized projection from an augmented stage row to its tail. -/
def stageRowProjection (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :=
  SplitRealizationFiber.projection (stageFirstTail r W n)

lemma stageRowProjection_eq (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    stageRowProjection r W n = (SSet.toTop.map ((stagePathProjection r W).app (op n))).hom := by
  change (SSet.toTop.map (stageFirstTail r W n) ≫ SSet.toTop.map (snd _ _)).hom = _
  rw [← CategoryTheory.Functor.map_comp, stageFirstTail_snd]

/-- The stage-fiber insertion into the homotopy fiber of the row projection. -/
def stageRowFiberComparison (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :=
  SplitRealizationFiber.inclusion (stageFirstTail r W n) ((stagePathFiber r W).app (op n))
    (stageVertex r ((rows n).obj W)) (stagePathFiber_firstTail r W n)

theorem stageRowFiberComparison_weak (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n :
  SimplexCategory) :
    IsWeakHomotopyEquivalence (stageRowFiberComparison r W n) :=
  isWeakHomotopyEquivalence_of_point _ (stagePoint r W)
    (SplitRealizationFiber.inclusion_bijective (stageFirstTail r W n) ((stagePathFiber r W).app
      (op n))
      (stageVertex r ((rows n).obj W)) (stagePathFiber_firstTail r W n)
      (stageFirstTailRealizationEquiv r W n) (stageFirstTailRealizationEquiv_toFun r W n))

/-- The original ordinal squares remain weakly cartesian at every finite iterated stage. -/
theorem stagePathProjection_transition (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    TransitionWeakCartesian (Functor.whiskerLeft TwoSidedBar.indexProjection
      (stagePathProjection r W)) := by
  intro d e f
  let m := TwoSidedBar.indexProjection.obj d
  let n := TwoSidedBar.indexProjection.obj e
  let α := TwoSidedBar.indexProjection.map f
  let : PathConnectedSpace |(stages r).obj W| := stageSpace_pathConnected r W
  let : PathConnectedSpace |(stages r).obj ((rows (addInitial.obj m.unop)).obj W)| :=
    stageSpace_pathConnected r ((rows (addInitial.obj m.unop)).obj W)
  let : PathConnectedSpace |(stages r).obj ((rows m.unop).obj W)| :=
    stageSpace_pathConnected r ((rows m.unop).obj W)
  have hsquare : (pathDiagram W ⋙ stages r).map α ≫ stageFirstTail r W n.unop ≫ snd _ _ =
      stageFirstTail r W m.unop ≫ snd _ _ ≫ (rowDiagram W ⋙ stages r).map α := by
    rw [stageFirstTail_snd, ← Category.assoc, stageFirstTail_snd]
    exact (stagePathProjection r W).naturality α
  have hsection : (stagePathFiber r W).app m ≫ (pathDiagram W ⋙ stages r).map α =
      (stagePathFiber r W).app n := by
    have h := ((stagePathFiber r W).naturality α).symm
    simp only [Functor.const_obj_map] at h
    exact h
  have h := SplitRealizationFiber.comparison_isWeakHomotopyEquivalence
    (stageFirstTail r W m.unop) (stageFirstTail r W n.unop)
    ((stagePathFiber r W).app m) ((stagePathFiber r W).app n)
    (stageVertex r ((rows m.unop).obj W)) (stageVertex r ((rows n.unop).obj W))
    (stagePathFiber_firstTail r W m.unop) (stagePathFiber_firstTail r W n.unop)
    ((pathDiagram W ⋙ stages r).map α) ((rowDiagram W ⋙ stages r).map α)
    hsquare hsection (stageFirstTailRealizationEquiv r W m.unop)
    (stageFirstTailRealizationEquiv_toFun r W m.unop)
    (stageFirstTailRealizationEquiv r W n.unop) (stageFirstTailRealizationEquiv_toFun r W n.unop)
    (stagePoint r W)
  exact Topology.HomotopyPullback.WeakCartesian.congr h (stageRowProjection_eq r W m.unop)
    (stageRowProjection_eq r W n.unop) rfl rfl

open Fibration Fibration.RelativeRows TheoremA TwoSidedBar

/-- The original constant-row fiber inclusion at every iterated stage. -/
def stageTotalFiberInclusion (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    (stages r).obj W ⟶ diagonalSSet (pathDiagram W ⋙ stages r) :=
  (diagonalConstantIso _).inv ≫ diagonalMap (stagePathFiber r W)

/-- The realized diagonal tail map from the path diagram to the next stage. -/
def stageTotalTailMap (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    C(|diagonalSSet (pathDiagram W ⋙ stages r)|, stageSpace (r+1) W) :=
  (SSet.toTop.map (diagonalMap (stagePathProjection r W))).hom

lemma stageTotalFiberInclusion_tail (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    stageTotalFiberInclusion r W ≫ diagonalMap (stagePathProjection r W) =
      SSet.const (stageVertex (r+1) W) := by
  ext n A : 4
  change ((stages r).map (rowTail W n.unop)).app n
      (((stages r).map (rowFiber W n.unop)).app n A) =
    ((stages r).obj ((rows n.unop).obj W)).map (n.unop.const ⦋0⦌ 0).op
      (((stages r).map ((rowsReindex (n.unop.const ⦋0⦌ 0)).app W)).app (op ⦋0⦌)
        (stageVertex r ((rows ⦋0⦌).obj W)))
  rw [stageVertex_naturality]
  have h := congrArg (fun f ↦ ((stages r).map f).app n) (rowFiber_tail W n.unop)
  rw [CategoryTheory.Functor.map_comp, stages_map_zeroHom] at h
  exact ConcreteCategory.congr_hom h A

lemma stageTotalTailMap_fiberInclusion (r : ℕ) (W : WideSubcategory preservesZero.{u}) (x :
  stageSpace r W) :
    stageTotalTailMap r W (SSet.toTop.map (stageTotalFiberInclusion r W) x) = stagePoint (r+1) W
      := by
  change (SSet.toTop.map (stageTotalFiberInclusion r W) ≫
    SSet.toTop.map (diagonalMap (stagePathProjection r W))) x = _
  rw [← CategoryTheory.Functor.map_comp, stageTotalFiberInclusion_tail]
  exact realization_const_apply _ x

/-- The total stage-fiber inclusion with its specified constant homotopy-fiber path. -/
def stageTotalFiberComparison (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    C(stageSpace r W, HomotopyFiber (stageTotalTailMap r W) (stagePoint (r+1) W)) where
  toFun x := HomotopyFiber.basepoint _ _ (SSet.toTop.map (stageTotalFiberInclusion r W) x)
    (stageTotalTailMap_fiberInclusion r W x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (SSet.toTop.map (stageTotalFiberInclusion r W)).hom.continuous.prodMk continuous_const

/-- The exact total comparison is weak at every stage, using the proved row additivity. -/
theorem stageTotalFiberComparison_weak (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    IsWeakHomotopyEquivalence (stageTotalFiberComparison r W) := by
  let b := realizationPoint (stageVertex r ((rows ⦋0⦌).obj W))
  let e₀ := HomotopyFiber.congrHomeomorph (stageRowProjection_eq r W ⦋0⦌) (rfl : b = b)
  let e₁ := HomotopyFiber.congrHomeomorph
    (rfl : (SSet.toTop.map (diagonalMap (stagePathProjection r W))).hom = stageTotalTailMap r W)
    (evaluation_barZero_realizationPoint (rowDiagram W ⋙ stages r) (stageVertex r ((rows
      ⦋0⦌).obj W)))
  have h := (isWeakHomotopyEquivalence_of_homotopyEquiv e₁.toHomotopyEquiv).comp
    ((zeroDiagonalFiberMap_isWeakHomotopyEquivalence (stagePathProjection r W)
      (stagePathProjection_transition r W) b).comp
      ((isWeakHomotopyEquivalence_of_homotopyEquiv e₀.toHomotopyEquiv).comp
        (stageRowFiberComparison_weak r W ⦋0⦌)))
  have heq : stageTotalFiberComparison r W = e₁.toHomotopyEquiv.toFun.comp
      ((zeroDiagonalFiberMap (stagePathProjection r W) b).comp
        (e₀.toHomotopyEquiv.toFun.comp (stageRowFiberComparison r W ⦋0⦌))) := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    apply _root_.Prod.ext
    · change SSet.toTop.map (stageTotalFiberInclusion r W) x =
        SSet.toTop.map (evaluationMap (pathDiagram W ⋙ stages r))
          (SSet.toTop.map (barZeroInclusion (pathDiagram W ⋙ stages r))
            (SSet.toTop.map ((stagePathFiber r W).app (op ⦋0⦌)) x))
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact congrArg (fun f ↦ SSet.toTop.map f x)
        (barZeroInclusion_evaluation_section (stagePathFiber r W)).symm
    · apply ContinuousMap.ext
      intro t
      exact (evaluation_barZero_realizationPoint (rowDiagram W ⋙ stages r)
        (stageVertex r ((rows ⦋0⦌).obj W))).symm
  rw [heq]
  exact h


end CategoryTheory.Waldhausen.IteratedS
