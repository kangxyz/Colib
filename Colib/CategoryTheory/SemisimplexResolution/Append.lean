/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.SemisimplexResolution.Basic
public import Colib.CategoryTheory.ComposableArrows.Append

/-!
# Appending the common target of a strict semisimplex face

The extended index map is injective, includes the old face exactly, and sends
the appended vertex to the appended vertex. The face theorem uses the original
comma square and controls every old map as well as the new terminal arrow.

Implementation provenance:
`Quillen/CategoryTheory/SemisimplexResolution/Append.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
universe u
namespace CategoryTheory.SemisimplexResolution
open CategoryTheory.ComposableArrows
variable (C : Type u) [SmallCategory C]

/-- Extend an order embedding by the new terminal index. -/
def appendIndex {n m : ℕ} (a : Fin (n + 1) ↪o Fin (m + 1)) :
    Fin (n+2) ↪o Fin (m+2) :=
  OrderEmbedding.ofStrictMono
    (Fin.lastCases (Fin.last (m + 1)) (fun i => (a i).castSucc)) (by
      intro i j hij
      induction i using Fin.lastCases with
      | last => exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using a.strictMono (show i < j from hij))

@[simp] theorem appendIndex_castSucc {n m : ℕ} (a : Fin (n + 1) ↪o Fin (m + 1))
    (i : Fin (n + 1)) : appendIndex a i.castSucc = (a i).castSucc := by
  simp [appendIndex]

@[simp] theorem appendIndex_last {n m : ℕ} (a : Fin (n + 1) ↪o Fin (m + 1)) :
    appendIndex a (Fin.last (n + 1)) = Fin.last (m + 1) := by
  simp [appendIndex]

variable {C}

/-- Appending a target preserves the full old chain strictly. -/
theorem appendChain_restrict {n : ℕ} (A : ComposableArrows C n) {Y : C}
    (q : A.obj (Fin.last n) ⟶ Y) :
    Fin.castSuccFunctor (n + 1) ⋙ appendChain A q = A :=
  Functor.ext_of_iso (appendChainRestrictionIso A q)
    (appendChain_obj_castSucc A q) (by intro i; rfl)


/-- Face compatibility of the displayed maps from every old vertex to a target. -/
theorem face_to_target {A B : Obj C} (f : A ⟶ B) {d : C}
    (q : lastObj C A ⟶ d) (r : lastObj C B ⟶ d)
    (sq : lastMap C f ≫ r = q) (i : Fin (A.dim + 1)) :
    B.chain.map (homOfLE (Fin.le_last (f.index i))) ≫ r =
      eqToHom (congrArg (fun T : ComposableArrows C A.dim => T.obj i) f.face) ≫
        A.chain.map (homOfLE (Fin.le_last i)) ≫ q := by
  have hs := congrArg (fun k =>
    eqToHom (congrArg (fun T : ComposableArrows C A.dim =>
      T.obj (Fin.last A.dim)) f.face) ≫ k) sq
  simp only [lastMap, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp] at hs
  rw [show homOfLE (Fin.le_last (f.index i)) =
    (indexFunctor f.index).map (homOfLE (Fin.le_last i)) ≫
      homOfLE (Fin.le_last (f.index (Fin.last A.dim))) from Subsingleton.elim _ _,
    B.chain.map_comp, Category.assoc, hs, ← Category.assoc, face_map]
  simp only [Category.assoc]

/-- Object equality for a face embedding with an appended common target. -/
theorem append_face_obj {A B : Obj C} (f : A ⟶ B) {d : C}
    (q : lastObj C A ⟶ d) (r : lastObj C B ⟶ d)
    (i : Fin (A.dim + 2)) :
    (indexFunctor (appendIndex f.index) ⋙ appendChain B.chain r).obj i =
      (appendChain A.chain q).obj i := by
  induction i using Fin.lastCases with
  | last =>
    change (appendChain B.chain r).obj (appendIndex f.index (Fin.last (A.dim + 1))) = _
    rw [appendIndex_last, appendChain_obj_last, appendChain_obj_last]
  | cast i =>
    change (appendChain B.chain r).obj (appendIndex f.index i.castSucc) = _
    rw [appendIndex_castSucc, appendChain_obj_castSucc, appendChain_obj_castSucc]
    exact congrArg (fun T : ComposableArrows C A.dim => T.obj i) f.face

theorem appendChain_map_castSucc {n : ℕ} (A : ComposableArrows C n) {d : C}
    (q : A.obj (Fin.last n) ⟶ d) {i j : Fin (n + 1)} (h : i ⟶ j) :
    (appendChain A q).map ((Fin.castSuccFunctor (n + 1)).map h) =
      eqToHom (appendChain_obj_castSucc A q i) ≫ A.map h ≫
        eqToHom (appendChain_obj_castSucc A q j).symm := by
  apply (cancel_mono (eqToHom (appendChain_obj_castSucc A q j))).1
  simpa [appendChainRestrictionIso, Category.assoc] using
    (appendChainRestrictionIso A q).hom.naturality h

theorem appendChain_map_to_last {n : ℕ} (A : ComposableArrows C n) {d : C}
    (q : A.obj (Fin.last n) ⟶ d) (i : Fin (n + 1)) :
    (appendChain A q).map (homOfLE (Fin.le_last i.castSucc)) =
      eqToHom (appendChain_obj_castSucc A q i) ≫
        A.map (homOfLE (Fin.le_last i)) ≫ q ≫
        eqToHom (appendChain_obj_last A q).symm := by
  apply (cancel_mono (eqToHom (appendChain_obj_last A q))).1
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
    appendChain_to_last A q i

theorem appendIndex_map_castSucc {n m : ℕ} (a : Fin (n + 1) ↪o Fin (m + 1))
    {i j : Fin (n + 1)} (h : i ⟶ j) :
    (indexFunctor (appendIndex a)).map ((Fin.castSuccFunctor (n + 1)).map h) =
      eqToHom (appendIndex_castSucc a i) ≫
        (Fin.castSuccFunctor (m + 1)).map ((indexFunctor a).map h) ≫
        eqToHom (appendIndex_castSucc a j).symm := Subsingleton.elim _ _

theorem appendIndex_map_to_last {n m : ℕ} (a : Fin (n + 1) ↪o Fin (m + 1))
    (i : Fin (n + 1)) :
    (indexFunctor (appendIndex a)).map (homOfLE (Fin.le_last i.castSucc)) =
      eqToHom (appendIndex_castSucc a i) ≫
        homOfLE (Fin.le_last (a i).castSucc) ≫
        eqToHom (appendIndex_last a).symm := Subsingleton.elim _ _

/-- The full appended face is the original source chain, including its last arrow. -/
theorem append_face {A B : Obj C} (f : A ⟶ B) {d : C}
    (q : lastObj C A ⟶ d) (r : lastObj C B ⟶ d)
    (sq : lastMap C f ≫ r = q) :
    indexFunctor (appendIndex f.index) ⋙ appendChain B.chain r = appendChain A.chain q := by
  refine CategoryTheory.Functor.ext (append_face_obj f q r) ?_
  intro i j h
  induction i using Fin.lastCases with
  | last =>
    have hj : j = Fin.last (A.dim + 1) := le_antisymm (Fin.le_last _) (leOfHom h)
    subst j
    simp only [Subsingleton.elim h (𝟙 _), CategoryTheory.Functor.map_id, Category.id_comp,
      eqToHom_trans, eqToHom_refl]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      have hs := face_to_target f q r sq i
      rw [show h = homOfLE (Fin.le_last i.castSucc) from Subsingleton.elim _ _]
      simp only [CategoryTheory.Functor.comp_map, appendIndex_map_to_last,
        CategoryTheory.Functor.map_comp, eqToHom_map,
        appendChain_map_to_last, Category.assoc]
      rw [← Category.assoc (B.chain.map _) r, hs]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    | cast j =>
      let hij : i ⟶ j := homOfLE (leOfHom h)
      have hf := face_map C f hij
      have hf' := congrArg (fun k => k ≫ eqToHom
        (congrArg (fun T : ComposableArrows C A.dim => T.obj j) f.face).symm) hf
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hf'
      rw [show h = (Fin.castSuccFunctor (A.dim + 1)).map hij from Subsingleton.elim _ _]
      simp only [CategoryTheory.Functor.comp_map, appendIndex_map_castSucc,
        CategoryTheory.Functor.map_comp, eqToHom_map,
        appendChain_map_castSucc, Category.assoc]
      rw [hf']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]


end CategoryTheory.SemisimplexResolution
