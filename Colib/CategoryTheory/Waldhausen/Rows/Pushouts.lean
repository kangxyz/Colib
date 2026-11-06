/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Basic
public import Colib.CategoryTheory.Waldhausen.Rows.ReedyCofibrations
public import Colib.CategoryTheory.Waldhausen.Rows.PointwisePushouts
public import Colib.CategoryTheory.Waldhausen.Rows.RelativePushout
public import Colib.CategoryTheory.Limits.PointwisePushoutInterchange

/-! # Genuine pushouts of quotient rows

Rows remain actual quotient grids under pointwise pushouts along the
all-triples Reedy cofibrations. The quotient squares follow from actual
pushout interchange, rather than a closure or exactness assumption.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/Pushouts.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C) {n : SimplexCategory}

/-- The actual pointwise pushout diagram is again a genuine S-quotient row. -/
theorem isRow_of_pointwise_pushout {A B D : Obj W n} {P : Interval n ⥤ C}
    (f : A ⟶ B) (g : A ⟶ D) (i : B.obj ⟶ P) (j : D.obj ⟶ P)
    (hf : cof W n f)
    (hp : ∀ p, IsPushout (f.hom.app p) (g.hom.app p) (i.app p) (j.app p)) : IsRow W P where
  zero p := by
    let : IsIso (f.hom.app (interval p p le_rfl)) :=
      (A.property.zero p).isIso (B.property.zero p) _
    let : IsIso (j.app (interval p p le_rfl)) := (hp _).isIso_inr_of_isIso
    exact (D.property.zero p).of_iso (asIso (j.app (interval p p le_rfl))).symm
  cofibration a b c hab hbc := by
    let I : ((horizontalArrow W a b c hab hbc).obj B).obj ⟶
        Arrow.mk (P.map (homOfLE (show interval a b hab ≤ interval a c (hab.trans hbc) from
          ⟨le_rfl, hbc⟩))) := Arrow.homMk (i.app _) (i.app _) (i.naturality _).symm
    let J : ((horizontalArrow W a b c hab hbc).obj D).obj ⟶
        Arrow.mk (P.map (homOfLE (show interval a b hab ≤ interval a c (hab.trans hbc) from
          ⟨le_rfl, hbc⟩))) := Arrow.homMk (j.app _) (j.app _) (j.naturality _).symm
    exact arrow_cof_of_pointwise_pushouts W
      ((horizontalArrow W a b c hab hbc).map f) ((horizontalArrow W a b c hab hbc).map g)
      I J (hp _) (hp _) (hf a b c hab hbc)
  quotient a b c hab hbc :=
    isPushout_of_pointwise_pushouts f.hom g.hom i j hp _ _ _ _
      (Subsingleton.elim _ _) (A.property.quotient a b c hab hbc)
      (B.property.quotient a b c hab hbc) (D.property.quotient a b c hab hbc)

/-- In a displayed pointwise row pushout the new leg satisfies every Reedy test. -/
theorem cof_of_pointwise_pushout {A B D P : Obj W n}
    (f : A ⟶ B) (g : A ⟶ D) (i : B ⟶ P) (j : D ⟶ P)
    (hf : cof W n f)
    (hp : ∀ p, IsPushout (f.hom.app p) (g.hom.app p) (i.hom.app p) (j.hom.app p)) : cof W n j := by
  intro a b c hab hbc
  let H := horizontalArrow W a b c hab hbc
  have h : IsPushout (H.map f) (H.map g) (H.map i) (H.map j) :=
    IsPushout.of_map_of_faithful (ExtensionCategory.forget W)
      (ExtensionCategory.arrow_isPushout _ _ _ _ (hp _) (hp _))
  exact ExtensionCategory.cof_pushout W (hf a b c hab hbc) h

/-- Actual pushouts of quotient rows exist, are pointwise, and retain the Reedy cofibration. -/
theorem exists_row_pushout {A B D : Obj W n} (f : A ⟶ B) (g : A ⟶ D) (hf : cof W n f) :
    ∃ (P : Obj W n) (i : B ⟶ P) (j : D ⟶ P), IsPushout f g i j ∧
      (∀ p, IsPushout (f.hom.app p) (g.hom.app p) (i.hom.app p) (j.hom.app p)) ∧ cof W n j := by
  obtain ⟨P, i, j, h, hp⟩ := exists_pointwise_pushout W f.hom g.hom (cof_app W hf)
  let P' : Obj W n := ⟨P, isRow_of_pointwise_pushout W f g i j hf hp⟩
  let i' : B ⟶ P' := (objects W n).homMk i
  let j' : D ⟶ P' := (objects W n).homMk j
  exact ⟨P', i', j', IsPushout.of_map_of_faithful (forget W n) h, hp,
    cof_of_pointwise_pushout W f g i' j' hf hp⟩

/-- Every displayed row pushout along a Reedy cofibration is pointwise,
proved by comparison with the actual constructed pushout. -/
theorem pointwise_of_isPushout {A B D P : Obj W n}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
    (hf : cof W n f) (h : IsPushout f g i j) (p : Interval n) :
    IsPushout (f.hom.app p) (g.hom.app p) (i.hom.app p) (j.hom.app p) := by
  obtain ⟨P₀, i₀, j₀, h₀, hp, _⟩ := exists_row_pushout W f g hf
  let e : P₀ ≅ P := h₀.isoIsPushout _ _ h
  apply (hp p).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ((evaluation W p).mapIso e)
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp] using!
      congrArg (fun k ↦ k.hom.app p) (h₀.inl_isoIsPushout_hom _ _ h)
  · simpa only [Iso.refl_hom, Category.id_comp] using!
      congrArg (fun k ↦ k.hom.app p) (h₀.inr_isoIsPushout_hom _ _ h)

end CategoryTheory.Waldhausen.QuotientRows
