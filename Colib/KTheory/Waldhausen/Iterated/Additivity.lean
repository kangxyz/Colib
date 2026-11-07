/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Interchange
public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Stages
public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.PathDiagram
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.Realization
public import Colib.KTheory.Waldhausen.Fibration.AllWeak.OrdinaryRows
public import Colib.Topology.Realization.BisimplicialEquivalence

/-!
# Genuine first-object/tail additivity at every finite S-stage

The original first/tail map lands in the actual simplicial product. Its realization is a
homotopy equivalence in every degree, by induction using genuine row transposition and the
accepted degree-zero relative additivity theorem. The actual constant-row fiber section
has exactly identity first component and the displayed constant-zero tail.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/Additivity.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps,
complete weak-equivalence statements, fiber paths and independent original universes are
  retained. -/
@[expose] public section

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
open Fibration Fibration.RelativeRows

/-- Evaluate an augmented quotient row on its first interval. -/
def rowFirst (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) : (rows
  (addInitial.obj n)).obj W ⟶ W :=
  ⟨⟨QuotientRows.evaluation W.obj.waldhausen (firstInterval n),
    QuotientRows.evaluation_exact W.obj.waldhausen (firstInterval n)⟩, rfl⟩

/-- Forget the initial interval of an augmented quotient row. -/
def rowTail (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    (rows (addInitial.obj n)).obj W ⟶ (rows n).obj W :=
  (rowsReindex (tail.app n)).app W

/-- The literal higher-stage first-object/tail map takes values in the simplicial product. -/
def stageFirstTail (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    (stages r).obj ((rows (addInitial.obj n)).obj W) ⟶
      (stages r).obj W ⊗ (stages r).obj ((rows n).obj W) :=
  lift ((stages r).map (rowFirst W n)) ((stages r).map (rowTail W n))

lemma rowFirst_swap (W : WideSubcategory preservesZero.{u}) (m n : SimplexCategory) :
    (rowSwap W m (addInitial.obj n)).hom ≫ rowFirst ((rows m).obj W) n =
      (rows m).map (rowFirst W n) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

lemma rowTail_swap (W : WideSubcategory preservesZero.{u}) (m n : SimplexCategory) :
    (rows m).map (rowTail W n) ≫ (rowSwap W m n).hom =
      (rowSwap W m (addInitial.obj n)).hom ≫ rowTail ((rows m).obj W) n := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact QuotientRows.transposeRows_reindex_inner W.obj.waldhausen (tail.app n)

/-- Genuine all-weak acyclicity gives the literal inverse of the original relative inclusion. -/
def allWeakRelativeLift (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    QuotientRows.Obj W.obj.waldhausen (addInitial.obj n) ⥤ RelativeRows.Obj (AllWeak.nested
      W.obj.waldhausen) n :=
  (RelativeRows.objects (AllWeak.nested W.obj.waldhausen) n).lift (𝟭 _)
    (fun _ _ ↦ AllWeak.acyclic W.obj.waldhausen _)

lemma allWeakRelativeLift_exact (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    IsExact ((rows (addInitial.obj n)).obj W).obj.waldhausen.cof
      ((rows (addInitial.obj n)).obj W).obj.waldhausen.weq
      (RelativeRows.waldhausenStructure (AllWeak.nested W.obj.waldhausen) n).cof
      (RelativeRows.waldhausenStructure (AllWeak.nested W.obj.waldhausen) n).weq
      (allWeakRelativeLift W n) where
  zero h := IsZero.of_full_of_faithful_of_isZero (RelativeRows.forget _ n) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := IsPushout.of_map_of_faithful (RelativeRows.forget _ n) h

/-- Identify the zero-stage augmented quotient rows with the all-weak relative rows. -/
def allWeakRelativeSSetIso (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    (stages 0).obj ((rows (addInitial.obj n)).obj W) ≅
      (relativeSRows (AllWeak.nested W.obj.waldhausen)).obj (op n) where
  hom := sSetMap (allWeakRelativeLift_exact W n)
  inv := sSetMap (RelativeRows.forget_exact (AllWeak.nested W.obj.waldhausen) n)
  hom_inv_id := by ext k A : 4; rfl
  inv_hom_id := by ext k A : 4; rfl

/-- The accepted genuine relative additivity theorem is exactly the degree-zero first/tail map. -/
theorem stageFirstTail_zero_equivalence (W : WideSubcategory preservesZero.{u}) (n :
  SimplexCategory) :
    IsRealizationEquivalence (stageFirstTail 0 W n) := by
  let eB : (stages 0).obj W ⊗ (stages 0).obj ((rows n).obj W) ≅
      sSet W.obj.waldhausen.cof W.obj.waldhausen.weq ⊗
        (ordinarySRows (acyclicStructure (AllWeak.nested W.obj.waldhausen))).obj (op n) :=
    tensorIso (Iso.refl _) ((AllWeak.ordinaryRowsIso W.obj.waldhausen).symm.app (op n))
  apply IsRealizationEquivalence.of_iso_square (stageFirstTail 0 W n)
    (firstTailSSet (AllWeak.nested W.obj.waldhausen) n) (allWeakRelativeSSetIso W n) eB
  · apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro A
    exact _root_.Prod.ext rfl rfl
  · exact ⟨firstTailSSetRealizationHomotopyEquiv (AllWeak.nested W.obj.waldhausen) n,
      firstTailSSetRealizationHomotopyEquiv_toFun (AllWeak.nested W.obj.waldhausen) n⟩

/-- The actual first/tail comparison before diagonalization in one more S-direction. -/
def firstTailDiagram (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    rowDiagram ((rows (addInitial.obj n)).obj W) ⋙ stages r ⟶
      (rowDiagram W ⋙ stages r) ⊗ (rowDiagram ((rows n).obj W) ⋙ stages r) :=
  lift (Functor.whiskerRight (rowDiagramFunctor.map (rowFirst W n)) (stages r))
    (Functor.whiskerRight (rowDiagramFunctor.map (rowTail W n)) (stages r))

lemma stageFirstTail_succ (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    stageFirstTail (r+1) W n = SSet.diagonalMap (firstTailDiagram r W n) := rfl

lemma firstTailDiagram_swap (r : ℕ) (W : WideSubcategory preservesZero.{u}) (m n :
  SimplexCategory) :
    (firstTailDiagram r W n).app (op m) ≫
      (tensorIso (Iso.refl _) ((stages r).mapIso (rowSwap W m n))).hom =
      ((stages r).mapIso (rowSwap W m (addInitial.obj n))).hom ≫
        stageFirstTail r ((rows m).obj W) n := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro A
  apply _root_.Prod.ext
  · have h := congrArg (fun f ↦ ((stages r).map f).app k) (rowFirst_swap W m n)
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app] at h
    exact (ConcreteCategory.congr_hom h A).symm
  · have h := congrArg (fun f ↦ ((stages r).map f).app k) (rowTail_swap W m n)
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app] at h
    exact ConcreteCategory.congr_hom h A

/-- Genuine relative additivity persists through every actual finite iterated S-stage. -/
theorem stageFirstTail_equivalence (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n :
  SimplexCategory) :
    IsRealizationEquivalence (stageFirstTail r W n) := by
  induction r generalizing W with
  | zero => exact stageFirstTail_zero_equivalence W n
  | succ r ih =>
    rw [stageFirstTail_succ]
    apply BisimplicialRealization.diagonalMap_isRealizationEquivalence
    intro m
    exact IsRealizationEquivalence.of_iso_square
      ((firstTailDiagram r W n).app (op ⦋m⦌))
      (stageFirstTail r ((rows ⦋m⦌).obj W) n)
      ((stages r).mapIso (rowSwap W ⦋m⦌ (addInitial.obj n)))
      (tensorIso (Iso.refl _) ((stages r).mapIso (rowSwap W ⦋m⦌ n)))
      (firstTailDiagram_swap r W ⦋m⦌ n) (ih ((rows ⦋m⦌).obj W))

open Fibration Fibration.RelativeRows

/-- Insert a row with the given first object and zero tail. -/
def rowFiber (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) : W ⟶ (rows
  (addInitial.obj n)).obj W :=
  (insertion (fiberOrdinal n)).app W

lemma rowFiber_first (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) : rowFiber W n
  ≫ rowFirst W n = 𝟙 W := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

lemma rowFiber_tail (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    rowFiber W n ≫ rowTail W n = zeroHom W ((rows n).obj W) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  change suspensionRow W.obj.waldhausen (fiberOrdinal n) ⋙
    QuotientRows.reindex W.obj.waldhausen (tail.app n) = (Functor.const _).obj (QuotientRows.zero
      W.obj.waldhausen n)
  rw [← suspensionRow_reindex]
  have h : tail.app n ≫ fiberOrdinal n = n.const ⦋1⦌ 1 := by ext i : 3; rfl
  rw [h]
  exact suspensionRow_const W.obj.waldhausen n 1

lemma rowFiber_reindex (W : WideSubcategory preservesZero.{u}) {m n : SimplexCategory} (α : m ⟶ n) :
    rowFiber W n ≫ (rowsReindex (addInitial.map α)).app W = rowFiber W m := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  change suspensionRow W.obj.waldhausen (fiberOrdinal n) ⋙
    QuotientRows.reindex W.obj.waldhausen (addInitial.map α) = suspensionRow W.obj.waldhausen
      (fiberOrdinal m)
  rw [← suspensionRow_reindex]
  congr 1
  ext i : 3
  cases i using Fin.cases <;> rfl

/-- The tail projection from the augmented path diagram to the row diagram. -/
def pathProjection (W : WideSubcategory preservesZero.{u}) : pathDiagram W ⟶ rowDiagram W where
  app n := rowTail W n.unop
  naturality n m α := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change QuotientRows.reindex W.obj.waldhausen (addInitial.map α.unop) ⋙
      QuotientRows.reindex W.obj.waldhausen (tail.app m.unop) =
      QuotientRows.reindex W.obj.waldhausen (tail.app n.unop) ⋙ QuotientRows.reindex
        W.obj.waldhausen α.unop
    rw [← QuotientRows.reindex_comp, ← QuotientRows.reindex_comp]
    congr 1

/-- The natural insertion from the constant model into the augmented path diagram. -/
def pathFiber (W : WideSubcategory preservesZero.{u}) : (Functor.const _).obj W ⟶ pathDiagram W
  where
  app n := rowFiber W n.unop
  naturality n m α := by
    change 𝟙 W ≫ rowFiber W m.unop = rowFiber W n.unop ≫
      (rowsReindex (addInitial.map α.unop)).app W
    rw [Category.id_comp]
    exact (rowFiber_reindex W α.unop).symm

/-- Apply the iterated-stage functor to the tail projection. -/
def stagePathProjection (r : ℕ) (W : WideSubcategory preservesZero.{u}) : pathDiagram W ⋙ stages
  r ⟶ rowDiagram W ⋙
    stages r :=
  Functor.whiskerRight (pathProjection W) (stages r)

/-- Apply the iterated-stage functor to the constant-model insertion. -/
def stagePathFiber (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    (Functor.const _).obj ((stages r).obj W) ⟶ pathDiagram W ⋙ stages r :=
  (Functor.constComp SimplexCategoryᵒᵖ W (stages r)).inv ≫
    Functor.whiskerRight (pathFiber W) (stages r)

lemma stageFirstTail_snd (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    stageFirstTail r W n ≫ snd _ _ = (stagePathProjection r W).app (op n) := by
  simp [stageFirstTail, stagePathProjection, pathProjection]

lemma stagePathFiber_firstTail (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n :
  SimplexCategory) :
    (stagePathFiber r W).app (op n) ≫ stageFirstTail r W n =
      ProductRealization.vertexSection ((stages r).obj W) ((stages r).obj ((rows n).obj W))
        (stageVertex r ((rows n).obj W)) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro A
  apply _root_.Prod.ext
  · have h := congrArg (fun f ↦ ((stages r).map f).app k) (rowFiber_first W n)
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      NatTrans.comp_app] at h
    exact ConcreteCategory.congr_hom h A
  · have h := congrArg (fun f ↦ ((stages r).map f).app k) (rowFiber_tail W n)
    rw [CategoryTheory.Functor.map_comp, stages_map_zeroHom] at h
    exact ConcreteCategory.congr_hom h A


end CategoryTheory.Waldhausen.IteratedS
