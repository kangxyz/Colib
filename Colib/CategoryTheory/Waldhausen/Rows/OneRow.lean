/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Reindex
public import Colib.CategoryTheory.Waldhausen.Rows.ReindexExact
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Embeddings
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Whiskering

/-! # The genuine one-step quotient row

The three original interval objects are literally `0`, `X`, `0`. Every
horizontal relative cofibration test is either the identity-arrow or
zero-arrow embedding, so exactness uses actual relative pushouts.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/OneRow.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The original three interval positions of `[1]`. -/
def oneIndex : Interval ⦋1⦌ ⥤ Fin 3 :=
  (show Monotone (fun p : Interval ⦋1⦌ ↦
    (⟨p.val.1.val + p.val.2.val, by
      have hi := p.val.1.isLt; have hj := p.val.2.isLt;
      change p.val.1.val < 2 at hi; change p.val.2.val < 2 at hj; omega⟩ : Fin 3)) from
    fun _ _ h ↦ Nat.add_le_add h.1 h.2).functor

/-- The actual natural map from the chosen constant zero to the identity. -/
def oneZeroToId : (Functor.const C).obj W.zero ⟶ 𝟭 C where
  app X := W.isZero.to_ X
  naturality _ _ _ := W.isZero.eq_of_src _ _

/-- The actual natural map from the identity to the chosen constant zero. -/
def oneIdToZero : 𝟭 C ⟶ (Functor.const C).obj W.zero where
  app X := W.isZero.from_ X
  naturality _ _ _ := W.isZero.eq_of_tgt _ _

/-- The original natural three-object diagram. -/
def oneChain : Fin 3 ⥤ (C ⥤ C) :=
  ComposableArrows.mk₂ (oneZeroToId W) (oneIdToZero W)

/-- The original one-step quotient grid on `X`. -/
def oneDiagram (X : C) : Interval ⦋1⦌ ⥤ C := oneIndex ⋙ (oneChain W).flip.obj X

/-- All original row conditions hold on the actual diagram. -/
theorem oneDiagram_isRow (X : C) : IsRow W (oneDiagram W X) where
  zero i := by fin_cases i <;> exact W.isZero
  cofibration i j k hij hjk := by
    change i.val ≤ j.val at hij
    change j.val ≤ k.val at hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      solve
      | omega
      | exact False.elim (Nat.not_succ_le_zero 0 hij)
      | exact False.elim (Nat.not_succ_le_zero 0 hjk)
      | exact W.cof.id_mem _
      | exact W.cof_zero X
  quotient i j k hij hjk := by
    change i.val ≤ j.val at hij
    change j.val ≤ k.val at hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      solve
      | omega
      | exact False.elim (Nat.not_succ_le_zero 0 hij)
      | exact False.elim (Nat.not_succ_le_zero 0 hjk)
      | exact IsPushout.id_horiz _
      | exact IsPushout.of_id_snd

/-- Insert an original object as the sole nonzero quotient of a genuine row. -/
def oneEmbedding : C ⥤ Obj W ⦋1⦌ where
  obj X := ⟨oneDiagram W X, oneDiagram_isRow W X⟩
  map f := (objects W ⦋1⦌).homMk (Functor.whiskerLeft oneIndex ((oneChain W).flip.map f))
  map_id _ := by apply ObjectProperty.hom_ext; ext p; exact (oneChain W).obj _ |>.map_id _
  map_comp _ _ := by apply ObjectProperty.hom_ext; ext p; exact (oneChain W).obj _ |>.map_comp _ _

/-- The actual one-step embedding is genuinely exact. -/
theorem oneEmbedding_exact :
    IsExact W.cof W.weq (waldhausenStructure W ⦋1⦌).cof
      (waldhausenStructure W ⦋1⦌).weq (oneEmbedding W) where
  zero h := isZero_of_components W _ (by
    rintro ⟨⟨i,j⟩, hij⟩
    change i.val ≤ j.val at hij
    fin_cases i <;> fin_cases j <;> solve
    | omega
    | exact W.isZero
    | exact h)
  cofibration f hf := by
    intro i j k hij hjk
    change i.val ≤ j.val at hij
    change j.val ≤ k.val at hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      solve
      | omega
      | exact False.elim (Nat.not_succ_le_zero 0 hij)
      | exact False.elim (Nat.not_succ_le_zero 0 hjk)
      | exact (ExtensionCategory.cof W).id_mem _
      | exact (ExtensionCategory.zeroEmbedding_exact W).cofibration f hf
      | exact (ExtensionCategory.identityEmbedding_exact W).cofibration f hf
  weak f hf := by
    rintro ⟨⟨i,j⟩, hij⟩
    change i.val ≤ j.val at hij
    fin_cases i <;> fin_cases j <;> solve
    | omega
    | exact W.weq.id_mem _
    | exact hf
  pushout hf h := by
    apply isPushout_of_pointwise W
    rintro ⟨⟨i,j⟩, hij⟩
    change i.val ≤ j.val at hij
    fin_cases i <;> fin_cases j <;> solve
    | omega
    | exact IsPushout.id_horiz _
    | exact h

@[simp] theorem oneEmbedding_whole_obj (X : C) :
    ((oneEmbedding W).obj X).obj.obj (interval 0 1 (by decide)) = X := rfl
@[simp] theorem oneEmbedding_whole_map {X Y : C} (f : X ⟶ Y) :
    ((oneEmbedding W).map f).hom.app (interval 0 1 (by decide)) = f := rfl

end CategoryTheory.Waldhausen.QuotientRows
