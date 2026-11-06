/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Actual native restricted-span Q-arrows, comparison functors and realization maps are retained. -/

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryIsoComma
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-!
# Common-base lifting of quotient-isomorphism Q-arrows

An ambient Q-arrow that becomes invertible in the quotient has an actual
representative over one ordinary Serre-isomorphic base. Both endpoints
and the arrow lift together, using the ordinary pushout of a span.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Localization
namespace CategoryTheory.ExactCategory.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] CategoryTheory.ExactCategory.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
variable (P : ObjectProperty C) [P.IsSerreClass]

/-- Regard an ordinary Serre-isomorphism as an auxiliary object. -/
def auxiliaryOverMk {X N : C} (f : X ⟶ N) (hf : P.isoModSerre f) : AuxiliaryKernel P N :=
  ⟨QConstruction.of _ _ (Over.mk f), hf⟩

/-- Every leg of a span whose quotient Q-arrow is invertible is a
Serre-isomorphism in the original abelian category. -/
theorem span_isoModSerre_of_quotient_isIso {X Y : C} (s : QConstruction.AbelianSpan X Y)
    [IsIso ((quotientMapQ P).map (QConstruction.mkHom _ _ s))] :
    P.isoModSerre s.l ∧ P.isoModSerre s.r := by
  let t : QConstruction.AbelianSpan (P.isoModSerre.Q.obj X) (P.isoModSerre.Q.obj Y) :=
    ((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P
      P.isoModSerre.Q)).toQCompatibleFunctor.mapSpan s
  have : IsIso (QConstruction.mkHom _ _ t) := inferInstanceAs
    (IsIso ((quotientMapQ P).map (QConstruction.mkHom _ _ s)))
  obtain ⟨hl, hr⟩ := QConstruction.isIso_legs_of_isIso t
  exact ⟨(ObjectProperty.SerreClassLocalization.isIso_map_iff P.isoModSerre.Q P s.l).1 hl,
    (ObjectProperty.SerreClassLocalization.isIso_map_iff P.isoModSerre.Q P s.r).1 hr⟩

/-- The pushout span is genuinely a span over its common target. -/
def spanOverPushout {X Y : C} (s : QConstruction.AbelianSpan X Y) :
    Span (overDeflation (pushout s.l s.r)) (overInflation (pushout s.l s.r))
      (Over.mk (pushout.inl s.l s.r)) (Over.mk (pushout.inr s.l s.r)) where
  apex := Over.mk (s.l ≫ pushout.inl s.l s.r)
  l := Over.homMk s.l rfl
  r := Over.homMk s.r pushout.condition.symm
  wl := inferInstanceAs (Epi s.l)
  wr := inferInstanceAs (Mono s.r)

/-- The lifted ordinary span retains exactly the original ambient Q-arrow. -/
@[simp]
lemma spanOverPushout_forget {X Y : C} (s : QConstruction.AbelianSpan X Y) :
    (overForgetQ (pushout s.l s.r)).map (QConstruction.mkHom _ _ (spanOverPushout s)) =
      QConstruction.mkHom _ _ s := rfl

/-- A quotient-isomorphism span supplies auxiliary objects at both cospan endpoints. -/
def auxiliarySpanLift {X Y : C} (s : QConstruction.AbelianSpan X Y)
    (hl : P.isoModSerre s.l) (hr : P.isoModSerre s.r) :
    auxiliaryOverMk P (pushout.inl s.l s.r) (MorphismProperty.pushout_inl _ _ hr) ⟶
      auxiliaryOverMk P (pushout.inr s.l s.r) (MorphismProperty.pushout_inr _ _ hl) :=
  ObjectProperty.homMk (QConstruction.mkHom _ _ (spanOverPushout s))

@[simp]
lemma auxiliarySpanLift_forget {X Y : C} (s : QConstruction.AbelianSpan X Y)
    (hl : P.isoModSerre s.l) (hr : P.isoModSerre s.r) :
    (auxiliaryForgetQ P (pushout s.l s.r)).map (auxiliarySpanLift P s hl hr) =
      QConstruction.mkHom _ _ s := rfl

/-- Every ambient Q-arrow inverted by the quotient lifts together with its
endpoints over one ordinary base. No ordinary lift between the fixed endpoints
is assumed. -/
theorem exists_auxiliary_arrow_lift {X Y : C}
    (f : QConstruction.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X ⟶ QConstruction.of _ _ Y)
    [IsIso ((quotientMapQ P).map f)] :
    ∃ (N : C) (i : X ⟶ N) (p : Y ⟶ N) (hi : P.isoModSerre i) (hp : P.isoModSerre p)
      (_ : Mono i) (_ : Epi p)
      (g : auxiliaryOverMk P i hi ⟶ auxiliaryOverMk P p hp),
      (auxiliaryForgetQ P N).map g = f := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep f
  have : IsIso ((quotientMapQ P).map (QConstruction.mkHom _ _ s)) := by
    rw [show QConstruction.mkHom _ _ s = f from hs]
    infer_instance
  obtain ⟨hl, hr⟩ := span_isoModSerre_of_quotient_isIso P s
  exact ⟨pushout s.l s.r, pushout.inl s.l s.r, pushout.inr s.l s.r,
    MorphismProperty.pushout_inl _ _ hr, MorphismProperty.pushout_inr _ _ hl,
    inferInstance, inferInstance, auxiliarySpanLift P s hl hr, hs⟩

/-- The ordinary quotient isomorphism underlying a structured Q-isomorphism. -/
def isoStructuredOrdinaryIso {V : P.isoModSerre.Localization}
    (A : IsoStructuredComma P (QConstruction.of
      ((abelianExactStructure P.isoModSerre.Localization)).deflation
      ((abelianExactStructure P.isoModSerre.Localization)).inflation V)) :
    V ≅ P.isoModSerre.Q.obj A.obj.right.obj.of :=
  (QConstruction.exists_iso_of_isIso (hf := A.property) A.obj.hom).choose

lemma isoStructuredOrdinaryIso_hom {V : P.isoModSerre.Localization}
    (A : IsoStructuredComma P (QConstruction.of
      ((abelianExactStructure P.isoModSerre.Localization)).deflation
      ((abelianExactStructure P.isoModSerre.Localization)).inflation V)) :
    (((abelianExactStructure P.isoModSerre.Localization)).qIsoOfIso (isoStructuredOrdinaryIso P
      A)).hom = A.obj.hom :=
  (QConstruction.exists_iso_of_isIso (hf := A.property) A.obj.hom).choose_spec

/-- A Serre-isomorphic map from the source of a structured object determines
an ordinary quotient identification of its new base. -/
def auxiliaryArrowLiftBaseIso {V : P.isoModSerre.Localization}
    (A : IsoStructuredComma P (QConstruction.of
      ((abelianExactStructure P.isoModSerre.Localization)).deflation
      ((abelianExactStructure P.isoModSerre.Localization)).inflation V)) {N : C}
    (i : A.obj.right.obj.of ⟶ N) (hi : P.isoModSerre i) : P.isoModSerre.Q.obj N ≅ V := by
  have : IsIso (P.isoModSerre.Q.map i) := Localization.inverts _ _ _ hi
  exact (asIso (P.isoModSerre.Q.map i)).symm ≪≫ (isoStructuredOrdinaryIso P A).symm

/-- This chosen base identification lifts the source object exactly. -/
theorem auxiliaryArrowLiftBaseIso_obj {V : P.isoModSerre.Localization}
    (A : IsoStructuredComma P (QConstruction.of
      ((abelianExactStructure P.isoModSerre.Localization)).deflation
      ((abelianExactStructure P.isoModSerre.Localization)).inflation V)) {N : C}
    (i : A.obj.right.obj.of ⟶ N) (hi : P.isoModSerre i) :
    (auxiliaryToIsoStructuredWithBase P (auxiliaryArrowLiftBaseIso P A i hi)).obj
      (auxiliaryOverMk P i hi) = A := by
  apply ObjectProperty.FullSubcategory.ext
  refine StructuredArrow.obj_ext _ A.obj (by rfl) ?_
  change (auxiliaryQuotientObjIsoWithBase P (auxiliaryArrowLiftBaseIso P A i hi)
    (auxiliaryOverMk P i hi)).inv ≫ (quotientMapQ P).map (𝟙 A.obj.right) = A.obj.hom
  erw [(quotientMapQ P).map_id, Category.comp_id]
  have : IsIso (P.isoModSerre.Q.map i) := Localization.inverts _ _ _ hi
  have he : asIso (P.isoModSerre.Q.map i) ≪≫ auxiliaryArrowLiftBaseIso P A i hi =
      (isoStructuredOrdinaryIso P A).symm := by simp [auxiliaryArrowLiftBaseIso]
  change (((abelianExactStructure P.isoModSerre.Localization)).qIsoOfIso
    (asIso (P.isoModSerre.Q.map i) ≪≫ auxiliaryArrowLiftBaseIso P A i hi)).inv = A.obj.hom
  rw [he]
  exact isoStructuredOrdinaryIso_hom P A

/-- Every single arrow in the quotient isomorphism comma lifts, with both
endpoints and its exact triangle, to one ordinary auxiliary category. -/
theorem exists_isoStructured_arrow_lift {V : P.isoModSerre.Localization}
    {A B : IsoStructuredComma P (QConstruction.of
      ((abelianExactStructure P.isoModSerre.Localization)).deflation
      ((abelianExactStructure P.isoModSerre.Localization)).inflation V)} (f : A ⟶ B) :
    ∃ (N : C) (φ : P.isoModSerre.Q.obj N ≅ V) (X Y : AuxiliaryKernel P N) (g : X ⟶ Y)
      (hX : (auxiliaryToIsoStructuredWithBase P φ).obj X = A)
      (hY : (auxiliaryToIsoStructuredWithBase P φ).obj Y = B),
      (auxiliaryToIsoStructuredWithBase P φ).map g ≫ eqToHom hY = eqToHom hX ≫ f := by
  have : IsIso (A.obj.hom ≫ (quotientMapQ P).map f.hom.right) := by
    rw [StructuredArrow.w f.hom]
    infer_instance
  have : IsIso ((quotientMapQ P).map f.hom.right) :=
    IsIso.of_isIso_comp_left A.obj.hom _
  obtain ⟨N, i, p, hi, hp, _, _, g, hg⟩ := exists_auxiliary_arrow_lift P f.hom.right
  let φ := auxiliaryArrowLiftBaseIso P A i hi
  let X := auxiliaryOverMk P i hi
  let Y := auxiliaryOverMk P p hp
  let F := auxiliaryToIsoStructuredWithBase P φ
  have hX : F.obj X = A := auxiliaryArrowLiftBaseIso_obj P A i hi
  have hY : F.obj Y = B := by
    apply ObjectProperty.FullSubcategory.ext
    refine StructuredArrow.obj_ext _ B.obj (by rfl) ?_
    change (F.obj Y).obj.hom ≫ (quotientMapQ P).map (𝟙 B.obj.right) = B.obj.hom
    erw [(quotientMapQ P).map_id, Category.comp_id]
    have hFg := StructuredArrow.w (F.map g).hom
    have hXh : (F.obj X).obj.hom = A.obj.hom := by
      have hh := StructuredArrow.w (eqToHom hX).hom
      simp only [ObjectProperty.eqToHom_hom, StructuredArrow.eqToHom_right,
        eqToHom_refl] at hh
      erw [(quotientMapQ P).map_id, Category.comp_id] at hh
      exact hh
    change (F.obj X).obj.hom ≫ (quotientMapQ P).map ((auxiliaryForgetQ P N).map g) =
      (F.obj Y).obj.hom at hFg
    rw [hg, hXh, StructuredArrow.w f.hom] at hFg
    exact hFg.symm
  refine ⟨N, φ, X, Y, g, hX, hY, ?_⟩
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom,
    StructuredArrow.comp_right, StructuredArrow.eqToHom_right]
  change (auxiliaryForgetQ P N).map g ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.right
  simpa using hg

end CategoryTheory.ExactCategory.SerreLocalization
