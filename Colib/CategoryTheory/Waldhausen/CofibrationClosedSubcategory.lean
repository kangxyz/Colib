/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Genuine inherited Waldhausen structure from actual cofibration-pushout closure

The zero and every required pushout remain original ambient objects. All
morphisms and both inherited classes are unchanged under the actual full
inclusion. Preservation of arbitrary chosen pushouts is proved by comparison
with the constructed ambient pushout, rather than assumed.
Implementation provenance: adapted from `Quillen/Waldhausen/CofibrationClosedSubcategory.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This isolated draft has not been compiled.

-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.CofibrationClosedSubcategory
variable {C : Type u} [Category.{v} C] (W : Structure C) (P : ObjectProperty C)

/-- Structural closure under the actual chosen zero and actual cofibration pushouts. -/
structure Closed : Prop where
  zero_mem : P W.zero
  pushout_mem {A B D Q : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ Q} {j : D ⟶ Q}
    (hi : W.cof i) (h : IsPushout i f g j) : P A → P B → P D → P Q

variable (H : Closed W P)
include H

/-- The inherited chosen zero is literally the original ambient zero. -/
def zero : P.FullSubcategory := ⟨W.zero, H.zero_mem⟩

/-- The actual ambient zero supplies both unique maps in the full subcategory. -/
theorem isZero : IsZero (zero W P H) where
  unique_to X := by
    refine ⟨{ default := P.homMk (W.isZero.to_ X.obj), uniq := ?_ }⟩
    intro f
    exact ObjectProperty.hom_ext _ (W.isZero.eq_of_src _ _)
  unique_from X := by
    refine ⟨{ default := P.homMk (W.isZero.from_ X.obj), uniq := ?_ }⟩
    intro f
    exact ObjectProperty.hom_ext _ (W.isZero.eq_of_tgt _ _)

/-- A genuine ambient pushout stays in the predicate and gives the full-subcategory pushout. -/
theorem pushout_exists {A B D : P.FullSubcategory} (i : A ⟶ B) (f : A ⟶ D)
    (hi : W.cof i.hom) :
    ∃ (Q : P.FullSubcategory) (g : B ⟶ Q) (j : D ⟶ Q),
      IsPushout i f g j ∧ IsPushout i.hom f.hom g.hom j.hom := by
  obtain ⟨Q, g, j, h⟩ := W.pushout_exists i.hom f.hom hi
  let Q' : P.FullSubcategory := ⟨Q, H.pushout_mem hi h A.property B.property D.property⟩
  let g' : B ⟶ Q' := P.homMk g
  let j' : D ⟶ Q' := P.homMk j
  exact ⟨Q', g', j', IsPushout.of_map_of_faithful P.ι h, h⟩

/-- Every original full-subcategory pushout along a cofibration is the actual ambient pushout. -/
theorem inclusion_map_pushout {A B D Q : P.FullSubcategory}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ Q} {j : D ⟶ Q}
    (hi : W.cof i.hom) (h : IsPushout i f g j) :
    IsPushout i.hom f.hom g.hom j.hom := by
  obtain ⟨Q₀, g₀, j₀, h₀, hamb⟩ := pushout_exists W P H i f hi
  let e : Q₀ ≅ Q := h₀.isoIsPushout _ _ h
  apply hamb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (P.ι.mapIso e)
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.id_comp]
    exact congrArg (fun k ↦ k.hom) (h₀.inl_isoIsPushout_hom _ _ h)
  · simp only [Iso.refl_hom, Category.id_comp]
    exact congrArg (fun k ↦ k.hom) (h₀.inr_isoIsPushout_hom _ _ h)

/-- The inherited actual Waldhausen structure, with both literal ambient map classes. -/
def waldhausenStructure : Structure P.FullSubcategory where
  zero := zero W P H
  isZero := isZero W P H
  cof := W.cof.inverseImage P.ι
  weq := W.weq.inverseImage P.ι
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact W.cof_iso f.hom inferInstance
  weq_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact W.weq_iso f.hom inferInstance
  cof_zero X := by
    have h : ((isZero W P H).to_ X).hom = W.isZero.to_ X.obj := W.isZero.eq_of_src _ _
    change W.cof ((isZero W P H).to_ X).hom
    rw [h]
    exact W.cof_zero X.obj
  pushout_exists i f hi := by
    obtain ⟨Q, g, j, h, _⟩ := pushout_exists W P H i f hi
    exact ⟨Q, g, j, h⟩
  cof_pushout hi h := W.cof_pushout hi (inclusion_map_pushout W P H hi h)
  gluing := by
    intro A B D Q A' B' D' Q' i f g j i' f' g' j' a b d p hi hi' h h' ei ef eg ej ha hb hd
    exact W.gluing a.hom b.hom d.hom p.hom hi hi'
      (inclusion_map_pushout W P H hi h) (inclusion_map_pushout W P H hi' h')
      (congrArg (fun k ↦ k.hom) ei) (congrArg (fun k ↦ k.hom) ef)
      (congrArg (fun k ↦ k.hom) eg) (congrArg (fun k ↦ k.hom) ej) ha hb hd

/-- The unchanged full inclusion is genuinely exact. -/
theorem inclusion_exact : IsExact (waldhausenStructure W P H).cof (waldhausenStructure W P H).weq
    W.cof W.weq P.ι where
  zero h := W.isZero.of_iso (P.ι.mapIso (h.iso (isZero W P H)))
  cofibration _ h := h
  weak _ h := h
  pushout hi h := inclusion_map_pushout W P H hi h

/-- Target saturation is inherited through the literal full inclusion. -/
instance twoOutOfThree [W.weq.HasTwoOutOfThreeProperty] :
    (waldhausenStructure W P H).weq.HasTwoOutOfThreeProperty :=
  inferInstanceAs ((W.weq.inverseImage P.ι).HasTwoOutOfThreeProperty)

end CategoryTheory.Waldhausen.CofibrationClosedSubcategory

attribute [colib_tag "COL-0145",
  colib_ref "Waldhausen1985" "Sections 1.1-1.2, pp.320-321 and 326-327"
    "background" "Inheritance under closure containing every relevant ambient pushout apex"]
  CategoryTheory.Waldhausen.CofibrationClosedSubcategory.Closed
  CategoryTheory.Waldhausen.CofibrationClosedSubcategory.zero
  CategoryTheory.Waldhausen.CofibrationClosedSubcategory.isZero
  CategoryTheory.Waldhausen.CofibrationClosedSubcategory.pushout_exists
  CategoryTheory.Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
  CategoryTheory.Waldhausen.CofibrationClosedSubcategory.waldhausenStructure
  CategoryTheory.Waldhausen.CofibrationClosedSubcategory.inclusion_exact
  CategoryTheory.Waldhausen.CofibrationClosedSubcategory.twoOutOfThree
