/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.ArrowPushouts

/-! # The pointwise Waldhausen structure on the entire arrow category

Unlike the Reedy category of cofibration arrows, objects here are arbitrary
arrows and cofibrations are componentwise. All pushouts and gluing are proved
on the actual source and target squares, without any ambient cocompleteness.


Implementation provenance:
`Quillen/Waldhausen/ArrowCategory/Structure.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ArrowCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- An arbitrary arrow between zero objects is a genuine zero arrow object. -/
theorem isZero_of_components (X : Arrow C) (hl : IsZero X.left) (hr : IsZero X.right) : IsZero X
    where
  unique_to Y := by
    refine ⟨{ default := Arrow.homMk (hl.to_ _) (hr.to_ _) (hl.eq_of_src _ _), uniq := ?_ }⟩
    intro f
    exact Arrow.hom_ext _ _ (hl.eq_of_src _ _) (hr.eq_of_src _ _)
  unique_from Y := by
    refine ⟨{ default := Arrow.homMk (hl.from_ _) (hr.from_ _) (hr.eq_of_tgt _ _), uniq := ?_ }⟩
    intro f
    exact Arrow.hom_ext _ _ (hl.eq_of_tgt _ _) (hr.eq_of_tgt _ _)

/-- Commutative squares whose source and target component maps are both cofibrations in `W`. -/
def cof : MorphismProperty (Arrow C) :=
  W.cof.inverseImage Arrow.leftFunc ⊓ W.cof.inverseImage Arrow.rightFunc

/-- Commutative squares whose source and target component maps are both weak equivalences in
`W`. -/
def weq : MorphismProperty (Arrow C) :=
  W.weq.inverseImage Arrow.leftFunc ⊓ W.weq.inverseImage Arrow.rightFunc

instance cof_multiplicative : (cof W).IsMultiplicative := by unfold cof; infer_instance
instance weq_multiplicative : (weq W).IsMultiplicative := by unfold weq; infer_instance

/-- The identity arrow of the chosen zero object, serving as the zero object of the arrow
category. -/
def zero : Arrow C := Arrow.mk (𝟙 W.zero)

theorem isZero : IsZero (zero W) where
  unique_to f := by
    refine ⟨{ default := (Arrow.homMk (W.isZero.to_ f.left) (W.isZero.to_ f.right)
        (W.isZero.eq_of_src _ _)), uniq := ?_ }⟩
    intro η
    apply Arrow.hom_ext <;> exact W.isZero.eq_of_src _ _
  unique_from f := by
    refine ⟨{ default := (Arrow.homMk (W.isZero.from_ f.left) (W.isZero.from_ f.right)
        (W.isZero.eq_of_tgt _ _)), uniq := ?_ }⟩
    intro η
    apply Arrow.hom_ext <;> exact W.isZero.eq_of_tgt _ _

/-- A displayed pointwise square is the genuine pushout of arbitrary arrows. -/
theorem isPushout_of_pointwise {A B D P : Arrow C}
    (f : A ⟶ B) (g : A ⟶ D) (i : B ⟶ P) (j : D ⟶ P)
    (hl : IsPushout f.left g.left i.left j.left)
    (hr : IsPushout f.right g.right i.right j.right) : IsPushout f g i j :=
  ExtensionCategory.arrow_isPushout f g i j hl hr

/-- Component pushouts construct the actual pushout along a pointwise cofibration. -/
theorem exists_pointwise_pushout {A B D : Arrow C} (f : A ⟶ B) (g : A ⟶ D) (hf : cof W f) :
    ∃ (P : Arrow C) (i : B ⟶ P) (j : D ⟶ P), IsPushout f g i j ∧
      IsPushout f.left g.left i.left j.left ∧ IsPushout f.right g.right i.right j.right := by
  obtain ⟨L, li, lj, hL⟩ := W.pushout_exists f.left g.left hf.1
  obtain ⟨R, ri, rj, hR⟩ := W.pushout_exists f.right g.right hf.2
  let p : L ⟶ R := hL.desc (B.hom ≫ ri) (D.hom ≫ rj) (by
    rw [← Category.assoc, f.w, Category.assoc, hR.w,
      ← Category.assoc, ← g.w, Category.assoc])
  let i : B ⟶ Arrow.mk p := Arrow.homMk li ri (hL.inl_desc _ _ _)
  let j : D ⟶ Arrow.mk p := Arrow.homMk lj rj (hL.inr_desc _ _ _)
  exact ⟨Arrow.mk p, i, j, isPushout_of_pointwise f g i j hL hR, hL, hR⟩

/-- Every displayed pushout along a pointwise cofibration is genuinely pointwise. -/
theorem pointwise_of_isPushout {A B D P : Arrow C}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
    (hf : cof W f) (h : IsPushout f g i j) :
    IsPushout f.left g.left i.left j.left ∧ IsPushout f.right g.right i.right j.right := by
  obtain ⟨P₀, i₀, j₀, h₀, hl, hr⟩ := exists_pointwise_pushout W f g hf
  let e : P₀ ≅ P := h₀.isoIsPushout _ _ h
  constructor
  · apply hl.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Arrow.leftFunc.mapIso e)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg Arrow.Hom.left (h₀.inl_isoIsPushout_hom _ _ h)
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg Arrow.Hom.left (h₀.inr_isoIsPushout_hom _ _ h)
  · apply hr.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Arrow.rightFunc.mapIso e)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg Arrow.Hom.right (h₀.inl_isoIsPushout_hom _ _ h)
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg Arrow.Hom.right (h₀.inr_isoIsPushout_hom _ _ h)

/-- The entire arrow category has its genuine componentwise Waldhausen structure. -/
def waldhausenStructure : Structure (Arrow C) where
  zero := zero W
  isZero := isZero W
  cof := cof W
  weq := weq W
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact ⟨W.cof_iso _ (inferInstance : IsIso (Arrow.leftFunc.map f)),
      W.cof_iso _ (inferInstance : IsIso (Arrow.rightFunc.map f))⟩
  weq_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact ⟨W.weq_iso _ (inferInstance : IsIso (Arrow.leftFunc.map f)),
      W.weq_iso _ (inferInstance : IsIso (Arrow.rightFunc.map f))⟩
  cof_zero f := by
    have hl : ((isZero W).to_ f).left = W.isZero.to_ f.left := W.isZero.eq_of_src _ _
    have hr : ((isZero W).to_ f).right = W.isZero.to_ f.right := W.isZero.eq_of_src _ _
    change W.cof ((isZero W).to_ f).left ∧ W.cof ((isZero W).to_ f).right
    rw [hl, hr]
    exact ⟨W.cof_zero _, W.cof_zero _⟩
  pushout_exists f g hf := by
    obtain ⟨P, i, j, h, _, _⟩ := exists_pointwise_pushout W f g hf
    exact ⟨P, i, j, h⟩
  cof_pushout hf h :=
    ⟨W.cof_pushout hf.1 (pointwise_of_isPushout W hf h).1,
      W.cof_pushout hf.2 (pointwise_of_isPushout W hf h).2⟩
  gluing := by
    intro A B D P A' B' D' P' f g i j f' g' i' j' a b d p hf hf' h h' ef eg ei ej ha hb hd
    obtain ⟨hl, hr⟩ := pointwise_of_isPushout W hf h
    obtain ⟨hl', hr'⟩ := pointwise_of_isPushout W hf' h'
    exact ⟨W.gluing a.left b.left d.left p.left hf.1 hf'.1 hl hl'
      (congrArg Arrow.Hom.left ef) (congrArg Arrow.Hom.left eg)
      (congrArg Arrow.Hom.left ei) (congrArg Arrow.Hom.left ej) ha.1 hb.1 hd.1,
      W.gluing a.right b.right d.right p.right hf.2 hf'.2 hr hr'
      (congrArg Arrow.Hom.right ef) (congrArg Arrow.Hom.right eg)
      (congrArg Arrow.Hom.right ei) (congrArg Arrow.Hom.right ej) ha.2 hb.2 hd.2⟩

/-- Source evaluation is genuinely exact. -/
theorem source_exact : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq
    W.cof W.weq (Arrow.leftFunc : Arrow C ⥤ C) where
  zero h := W.isZero.of_iso (Arrow.leftFunc.mapIso (h.iso (isZero W)))
  cofibration _ h := h.1
  weak _ h := h.1
  pushout hf h := (pointwise_of_isPushout W hf h).1

/-- Target evaluation is genuinely exact. -/
theorem target_exact : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq
    W.cof W.weq (Arrow.rightFunc : Arrow C ⥤ C) where
  zero h := W.isZero.of_iso (Arrow.rightFunc.mapIso (h.iso (isZero W)))
  cofibration _ h := h.2
  weak _ h := h.2
  pushout hf h := (pointwise_of_isPushout W hf h).2

end CategoryTheory.Waldhausen.ArrowCategory
