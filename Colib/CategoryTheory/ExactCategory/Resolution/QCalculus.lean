/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.QConstruction.EdgeClass
public import Colib.CategoryTheory.ExactCategory.Functor.QConstruction
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! Adapted from `Quillen/Resolution/QCalculus.lean`.
Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd;
Aglib 2c34f185fa859e862661f939cd216b07bcccfb26.
Actual maps, universal properties, assumptions and universes retained. -/

/-! # Exact-category Q-arrow calculations used by resolution -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

@[simp] lemma qDeflation_id (X : C) : E.qDeflation (𝟙 X) (E.deflation_id X) = 𝟙 _ := rfl
@[simp] lemma qInflation_id (X : C) : E.qInflation (𝟙 X) (E.inflation_id X) = 𝟙 _ := rfl

lemma qDeflation_comp {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z)
    (hp : E.deflation p) (hq : E.deflation q) :
    E.qDeflation q hq ≫ E.qDeflation p hp =
      E.qDeflation (p ≫ q) (E.deflation_comp _ _ hp hq) := by
  apply E.q_comp_of_isPullback _ _ p (𝟙 X)
    (IsPullback.of_horiz_isIso (fst := 𝟙 X) (g := 𝟙 Y) ⟨by simp⟩).flip
    _ (Iso.refl _)
  · simp
  · simp

lemma qInflation_comp {X Y Z : C} (i : X ⟶ Y) (j : Y ⟶ Z)
    (hi : E.inflation i) (hj : E.inflation j) :
    E.qInflation i hi ≫ E.qInflation j hj =
      E.qInflation (i ≫ j) (E.inflation_comp _ _ hi hj) := by
  apply E.q_comp_of_isPullback _ _ (𝟙 X) i
    (IsPullback.of_horiz_isIso ⟨by simp⟩) _ (Iso.refl _)
  · simp
  · simp

/-- Postcomposition by an admissible inclusion simply composes the right leg. -/
lemma qSpan_comp_inflation {X Y Z : C} (s : Span E.deflation E.inflation X Y)
    (i : Y ⟶ Z) (hi : E.inflation i) :
    QConstruction.mkHom _ _ s ≫ E.qInflation i hi =
      QConstruction.mkHom _ _ ⟨s.apex, s.l, s.r ≫ i, s.wl, E.inflation_comp _ _ s.wr hi⟩ := by
  apply E.q_comp_of_isPullback _ _ (𝟙 s.apex) s.r
    (IsPullback.of_horiz_isIso ⟨by simp⟩)
    ⟨s.apex, s.l, s.r ≫ i, s.wl, E.inflation_comp _ _ s.wr hi⟩ (Iso.refl _)
  · simp
  · simp

/-- Precomposition by a reversed admissible epimorphism composes the left leg. -/
lemma qDeflation_comp_span {X Y Z : C} (p : Y ⟶ X) (hp : E.deflation p)
    (s : Span E.deflation E.inflation Y Z) :
    E.qDeflation p hp ≫ QConstruction.mkHom _ _ s =
      QConstruction.mkHom _ _ ⟨s.apex, s.l ≫ p, s.r, E.deflation_comp _ _ s.wl hp, s.wr⟩ := by
  apply E.q_comp_of_isPullback _ _ s.l (𝟙 s.apex)
    (IsPullback.of_horiz_isIso (fst := 𝟙 s.apex) (g := 𝟙 Y) ⟨by simp⟩).flip
    ⟨s.apex, s.l ≫ p, s.r, E.deflation_comp _ _ s.wl hp, s.wr⟩ (Iso.refl _)
  · simp
  · simp

/-- Forward admissible inclusions are monomorphisms in the genuine Q-category.
No fullness of an exact-subcategory inclusion is used. -/
instance qInflation_mono {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    Mono (E.qInflation i hi) where
  right_cancellation := by
    rintro ⟨⟨Z⟩⟩ ⟨s⟩ ⟨t⟩ h
    change QConstruction.mkHom _ _ s ≫ E.qInflation i hi =
      QConstruction.mkHom _ _ t ≫ E.qInflation i hi at h
    rw [E.qSpan_comp_inflation, E.qSpan_comp_inflation] at h
    obtain ⟨e, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 h
    let : Mono i := E.mono_of_inflation hi
    exact QConstruction.mkHom_eq_of_apexIso _ _ s t e hl
      ((cancel_mono i).1 (by simpa only [Category.assoc] using hr))

/-- The reverse-Q-arrow construction remembers its admissible epimorphism. -/
lemma qDeflation_injective {X Y : C} {p q : Y ⟶ X}
    (hp : E.deflation p) (hq : E.deflation q)
    (h : E.qDeflation p hp = E.qDeflation q hq) : p = q := by
  obtain ⟨e, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 h
  have he : e.hom = 𝟙 Y := by simpa using hr
  simpa [he] using hl.symm

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C : Type u} {D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

@[simp] lemma mapQ_qInflation (F : ExactFunctor EC ED)
    {X Y : C} (i : X ⟶ Y) (hi : EC.inflation i) :
    F.mapQ.map (EC.qInflation i hi) =
      ED.qInflation (F.toFunctor.map i) (F.map_inflation i hi) := by
  simp only [CategoryTheory.ExactCategory.ExactStructure.qInflation,
    CategoryTheory.ExactCategory.ExactFunctor.mapQ,
    QConstruction.CompatibleFunctor.mapQ_mkHom, QConstruction.CompatibleFunctor.mapSpan,
      CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ (Iso.refl (F.toFunctor.obj X)) <;> simp

@[simp] lemma mapQ_qDeflation (F : ExactFunctor EC ED)
    {X Y : C} (p : X ⟶ Y) (hp : EC.deflation p) :
    F.mapQ.map (EC.qDeflation p hp) =
      ED.qDeflation (F.toFunctor.map p) (F.map_deflation p hp) := by
  simp only [CategoryTheory.ExactCategory.ExactStructure.qDeflation,
    CategoryTheory.ExactCategory.ExactFunctor.mapQ,
    QConstruction.CompatibleFunctor.mapQ_mkHom, QConstruction.CompatibleFunctor.mapSpan,
      CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ (Iso.refl (F.toFunctor.obj X)) <;> simp

end CategoryTheory.ExactCategory.ExactFunctor
