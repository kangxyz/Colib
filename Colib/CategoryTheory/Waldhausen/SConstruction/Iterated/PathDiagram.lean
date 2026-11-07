/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Category
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Index
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# The actual added-initial-row path diagram and clamp

Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/PathObject.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, ordinal parameters, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet
open Fibration.RelativeRows

/-- Contract the added initial segment, retaining the actual remaining ordinal vertices. -/
def pathClamp {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) : addInitial.obj n ⟶ addInitial.obj n :=
  SimplexCategory.Hom.mk {
    toFun := Fin.cases 0 (fun i ↦ if τ.toOrderHom i = 0 then 0 else i.succ)
    monotone' := by
      intro i j hij
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => have h : i.val + 1 ≤ 0 := hij; omega
        | succ j =>
          have h : i ≤ j := Nat.le_of_succ_le_succ hij
          by_cases hi : τ.toOrderHom i = 0
          · simp only [Fin.cases_succ, hi, ite_true]; exact Fin.zero_le _
          · have hj : τ.toOrderHom j ≠ 0 := by
              intro hj
              have hm := τ.toOrderHom.monotone h
              rw [hj] at hm
              exact hi (Fin.le_zero_iff.mp hm)
            simp only [Fin.cases_succ, hi, hj, ite_false, Fin.succ_le_succ_iff]
            exact h }

lemma pathClamp_naturality {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    pathClamp (α ≫ τ) ≫ addInitial.map α = addInitial.map α ≫ pathClamp τ := by
  ext i : 3
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change (Fin.cases (motive := fun _ : Fin (m.len + 2) ↦ Fin (n.len + 2)) (0 : Fin (n.len +
      2)) (fun j ↦ (α.toOrderHom j).succ))
      (if τ.toOrderHom (α.toOrderHom i) = 0 then 0 else i.succ) =
      if τ.toOrderHom (α.toOrderHom i) = 0 then 0 else (α.toOrderHom i).succ
    split <;> rfl

lemma pathClamp_zero (n : SimplexCategory) :
    pathClamp (n.const ⦋1⦌ 0) = (addInitial.obj n).const (addInitial.obj n) 0 := by
  ext i : 3
  cases i using Fin.cases <;> rfl

lemma pathClamp_one (n : SimplexCategory) : pathClamp (n.const ⦋1⦌ 1) = 𝟙 (addInitial.obj n) := by
  ext i : 3
  cases i using Fin.cases <;> rfl

open Fibration.RelativeRows

/-- The row diagram augmented by an initial simplicial vertex. -/
def pathDiagram (W : WideSubcategory preservesZero.{u}) :
    SimplexCategoryᵒᵖ ⥤ WideSubcategory preservesZero.{u} :=
  addInitial.op ⋙ rowDiagram W

/-- The natural projection from the path diagram to the constant zero-ordinal row. -/
def pathAugmentation (W : WideSubcategory preservesZero.{u}) : pathDiagram W ⟶
    (Functor.const _).obj ((rows ⦋0⦌).obj W) where
  app n := (rowsReindex (⦋0⦌.const (addInitial.obj n.unop) 0)).app W
  naturality n m α := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change QuotientRows.reindex W.obj.waldhausen (addInitial.map α.unop) ⋙
      QuotientRows.reindex W.obj.waldhausen (⦋0⦌.const (addInitial.obj m.unop) 0) =
      QuotientRows.reindex W.obj.waldhausen (⦋0⦌.const (addInitial.obj n.unop) 0) ⋙ 𝟭 _
    rw [CategoryTheory.Functor.comp_id, ← QuotientRows.reindex_comp]
    congr 1

/-- The natural constant-row section of the path augmentation. -/
def pathSection (W : WideSubcategory preservesZero.{u}) :
    (Functor.const _).obj ((rows ⦋0⦌).obj W) ⟶ pathDiagram W where
  app n := (rowsReindex ((addInitial.obj n.unop).const ⦋0⦌ 0)).app W
  naturality n m α := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change 𝟭 _ ⋙ QuotientRows.reindex W.obj.waldhausen ((addInitial.obj m.unop).const ⦋0⦌ 0) =
      QuotientRows.reindex W.obj.waldhausen ((addInitial.obj n.unop).const ⦋0⦌ 0) ⋙
        QuotientRows.reindex W.obj.waldhausen (addInitial.map α.unop)
    rw [CategoryTheory.Functor.id_comp, ← QuotientRows.reindex_comp]
    congr 1

lemma pathSection_augmentation (W : WideSubcategory preservesZero.{u}) :
    pathSection W ≫ pathAugmentation W = 𝟙 _ := by
  ext n : 1
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  change QuotientRows.reindex W.obj.waldhausen ((addInitial.obj n.unop).const ⦋0⦌ 0) ⋙
    QuotientRows.reindex W.obj.waldhausen (⦋0⦌.const (addInitial.obj n.unop) 0) = 𝟭 _
  rw [← QuotientRows.reindex_comp]
  have h : ⦋0⦌.const (addInitial.obj n.unop) 0 ≫ (addInitial.obj n.unop).const ⦋0⦌ 0 = 𝟙 _ :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  rw [h, QuotientRows.reindex_id]

lemma pathClamp_reindex (W : WideSubcategory preservesZero.{u}) {m n : SimplexCategory}
    (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    (rowsReindex (addInitial.map α)).app W ≫ (rowsReindex (pathClamp (α ≫ τ))).app W =
      (rowsReindex (pathClamp τ)).app W ≫ (rowsReindex (addInitial.map α)).app W := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  change QuotientRows.reindex W.obj.waldhausen (addInitial.map α) ⋙
    QuotientRows.reindex W.obj.waldhausen (pathClamp (α ≫ τ)) =
      QuotientRows.reindex W.obj.waldhausen (pathClamp τ) ⋙
        QuotientRows.reindex W.obj.waldhausen (addInitial.map α)
  rw [← QuotientRows.reindex_comp, ← QuotientRows.reindex_comp, pathClamp_naturality]

/-- The actual added-initial-row contraction cylinder, before any weak-equivalence argument. -/
def pathCylinder (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    SSet.diagonalSSet (pathDiagram W ⋙ H) ⊗ Δ[1] ⟶
      SSet.diagonalSSet (pathDiagram W ⋙ H) where
  app n := ↾fun z ↦ (H.map ((rowsReindex (pathClamp z.2.down)).app W)).app n z.1
  naturality n m α := by
    ext z : 3
    change (H.map ((rowsReindex (pathClamp (α.unop ≫ z.2.down))).app W)).app m
      ((H.obj ((rows (addInitial.obj m.unop)).obj W)).map α
        ((H.map ((rowsReindex (addInitial.map α.unop)).app W)).app n z.1)) =
      (H.obj ((rows (addInitial.obj m.unop)).obj W)).map α
        ((H.map ((rowsReindex (addInitial.map α.unop)).app W)).app n
          ((H.map ((rowsReindex (pathClamp z.2.down)).app W)).app n z.1))
    have hn := ConcreteCategory.congr_hom
      ((H.map ((rowsReindex (pathClamp (α.unop ≫ z.2.down))).app W)).naturality α)
        ((H.map ((rowsReindex (addInitial.map α.unop)).app W)).app n z.1)
    refine hn.trans ?_
    apply congrArg ((H.obj ((rows (addInitial.obj m.unop)).obj W)).map α)
    have hm := congrArg (fun η : H.obj ((rows (addInitial.obj n.unop)).obj W) ⟶
        H.obj ((rows (addInitial.obj m.unop)).obj W) ↦ η.app n)
      (congrArg H.map (pathClamp_reindex W α.unop z.2.down))
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app] at hm
    exact ConcreteCategory.congr_hom hm z.1

/-- The diagonal simplicial map induced by the path augmentation. -/
def pathAugmentationMap (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :=
  SSet.diagonalMap (Functor.whiskerRight (pathAugmentation W) H)

/-- The diagonal simplicial map induced by the constant-row section. -/
def pathSectionMap (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :=
  SSet.diagonalMap (Functor.whiskerRight (pathSection W) H)

lemma pathSectionMap_augmentation (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    pathSectionMap H W ≫ pathAugmentationMap H W = 𝟙 _ := by
  let G := (Functor.whiskeringRight SimplexCategoryᵒᵖ
    (WideSubcategory preservesZero.{u}) SSet).obj H ⋙ SSet.diagonalFunctor
  change G.map (pathSection W) ≫ G.map (pathAugmentation W) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, pathSection_augmentation, CategoryTheory.Functor.map_id]

lemma pathCylinder_zero (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    SSet.ι₀ ≫ pathCylinder H W = pathAugmentationMap H W ≫ pathSectionMap H W := by
  ext n A : 4
  change (H.map ((rowsReindex (pathClamp (n.unop.const ⦋1⦌ 0))).app W)).app n A =
    (H.map ((pathSection W).app n)).app n ((H.map ((pathAugmentation W).app n)).app n A)
  rw [pathClamp_zero]
  have h : (rowsReindex ((addInitial.obj n.unop).const (addInitial.obj n.unop) 0)).app W =
      (pathAugmentation W).app n ≫ (pathSection W).app n := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact QuotientRows.reindex_comp W.obj.waldhausen
      ((addInitial.obj n.unop).const ⦋0⦌ 0) (⦋0⦌.const (addInitial.obj n.unop) 0)
  rw [h, CategoryTheory.Functor.map_comp]
  rfl

lemma pathCylinder_one (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    SSet.ι₁ ≫ pathCylinder H W = 𝟙 _ := by
  ext n A : 4
  change (H.map ((rowsReindex (pathClamp (n.unop.const ⦋1⦌ 1))).app W)).app n A = A
  rw [pathClamp_one]
  have h : (rowsReindex (𝟙 (addInitial.obj n.unop))).app W = 𝟙 _ := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact QuotientRows.reindex_id _ _
  rw [h, CategoryTheory.Functor.map_id]
  rfl

/-- The complete added-initial-row path object has the displayed original contraction. -/
def pathHomotopy (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    SSet.Homotopy (pathAugmentationMap H W ≫ pathSectionMap H W) (𝟙 _) where
  h := pathCylinder H W
  h₀ := pathCylinder_zero H W
  h₁ := pathCylinder_one H W
  rel := by ext n z; exact z.1.property.elim

lemma zeroRows_all_weak (W : WideSubcategory preservesZero.{u})
    {A B : ((rows ⦋0⦌).obj W).obj.Obj} (f : A ⟶ B) :
    ((rows ⦋0⦌).obj W).obj.waldhausen.weq f := by
  rintro ⟨⟨i,j⟩,hij⟩
  fin_cases i
  fin_cases j
  exact W.obj.waldhausen.weq_iso _ ((A.property.zero 0).isIso (B.property.zero 0) _)

end CategoryTheory.Waldhausen.IteratedS
