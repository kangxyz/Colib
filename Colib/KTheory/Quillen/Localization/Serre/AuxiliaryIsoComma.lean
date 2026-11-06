/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Actual native restricted-span Q-arrows, comparison functors and realization maps are retained. -/

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryBaseChange
public import Colib.KTheory.Quillen.Localization.Serre.LocalizationComma
public import Colib.CategoryTheory.QConstruction.Abelian.CospanComposition
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-!
# The actual comparison from an auxiliary category to an isomorphism comma

The structure map of each auxiliary object is inverted in the Serre
quotient. The comparison retains the actual ambient Q-arrow on morphisms.
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

/-- Forget the structure map of an auxiliary object and retain its ambient Q-object. -/
def auxiliaryForgetQ (N : C) : AuxiliaryKernel P N ⥤ (abelianExactStructure C).QCategory :=
  (auxiliaryKernelProperty P N).ι ⋙ overForgetQ N

instance auxiliary_quotient_structure_isIso {N : C} (X : AuxiliaryKernel P N) :
    IsIso (P.isoModSerre.Q.map X.obj.obj.of.hom) :=
  Localization.inverts P.isoModSerre.Q P.isoModSerre _ X.property

/-- The quotient of an auxiliary object is canonically identified with the base. -/
def auxiliaryQuotientObjIso {N : C} (X : AuxiliaryKernel P N) :
    (quotientMapQ P).obj ((auxiliaryForgetQ P N).obj X) ≅
      QConstruction.of ((abelianExactStructure P.isoModSerre.Localization)).deflation
        ((abelianExactStructure P.isoModSerre.Localization)).inflation
        (P.isoModSerre.Q.obj N) :=
  ((abelianExactStructure P.isoModSerre.Localization)).qIsoOfIso (asIso (P.isoModSerre.Q.map
    X.obj.obj.of.hom))

/-- A span over the base intertwines these actual quotient identifications. -/
theorem auxiliaryQuotientObjIso_naturality {N : C} {X Y : AuxiliaryKernel P N} (f : X ⟶ Y) :
    (quotientMapQ P).map ((auxiliaryForgetQ P N).map f) ≫ (auxiliaryQuotientObjIso P Y).hom =
      (auxiliaryQuotientObjIso P X).hom := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep f.hom
  let L := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits L P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits L P
  have : Epi s.l.left := s.wl
  have : Mono s.r.left := s.wr
  have hx : IsIso (L.map X.obj.obj.of.hom) := auxiliary_quotient_structure_isIso P X
  have hy : IsIso (L.map Y.obj.obj.of.hom) := auxiliary_quotient_structure_isIso P Y
  have hw : L.map s.l.left ≫ L.map X.obj.obj.of.hom =
      L.map s.r.left ≫ L.map Y.obj.obj.of.hom := by
    rw [← Functor.map_comp, Over.w s.l, ← Functor.map_comp, Over.w s.r]
  have : Mono (L.map s.l.left) := mono_of_mono_fac hw
  have : IsIso (L.map s.l.left) := isIso_of_mono_of_epi _
  have : IsIso (L.map s.r.left ≫ L.map Y.obj.obj.of.hom) := by rw [← hw]; infer_instance
  have : IsIso (L.map s.r.left) := IsIso.of_isIso_comp_right _ (L.map Y.obj.obj.of.hom)
  change (quotientMapQ P).map ((overForgetQ N).map f.hom) ≫ _ = _
  rw [← hs]
  let t := ((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P
    P.isoModSerre.Q)).toQCompatibleFunctor.mapSpan ((overForgetCompatible N).mapSpan
    s)
  change QConstruction.mkHom _ _ t ≫ QConstruction.inflationArrow (L.map Y.obj.obj.of.hom) =
    QConstruction.inflationArrow (L.map X.obj.obj.of.hom)
  have : IsIso t.l := inferInstanceAs (IsIso (L.map s.l.left))
  have : IsIso t.r := inferInstanceAs (IsIso (L.map s.r.left))
  rw [QConstruction.mkHom_eq_qIsoOfIso]
  change QConstruction.inflationArrow (inv (L.map s.l.left) ≫ L.map s.r.left) ≫
      QConstruction.inflationArrow (L.map Y.obj.obj.of.hom) =
      QConstruction.inflationArrow (L.map X.obj.obj.of.hom)
  rw [QConstruction.inflationArrow_comp]
  have hh : (inv (L.map s.l.left) ≫ L.map s.r.left) ≫ L.map Y.obj.obj.of.hom =
      L.map X.obj.obj.of.hom := by rw [Category.assoc, ← hw]; simp
  simp only [hh]

/-- The canonical fixed-base comparison into the quotient isomorphism comma. -/
def auxiliaryToIsoStructured (N : C) :
    AuxiliaryKernel P N ⥤ IsoStructuredComma P
      (QConstruction.of ((abelianExactStructure P.isoModSerre.Localization)).deflation
        ((abelianExactStructure P.isoModSerre.Localization)).inflation
        (P.isoModSerre.Q.obj N)) where
  obj X := ⟨StructuredArrow.mk (Y := (auxiliaryForgetQ P N).obj X)
    (auxiliaryQuotientObjIso P X).inv, by
      change IsIso (auxiliaryQuotientObjIso P X).inv
      infer_instance⟩
  map f := ObjectProperty.homMk (StructuredArrow.homMk ((auxiliaryForgetQ P N).map f) (by
    apply (cancel_mono (auxiliaryQuotientObjIso P _).hom).1
    simpa using congrArg ((auxiliaryQuotientObjIso P _).inv ≫ ·)
      (auxiliaryQuotientObjIso_naturality P f)))
  map_id X := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact (auxiliaryForgetQ P N).map_id X
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact (auxiliaryForgetQ P N).map_comp f g

/-- The comparison keeps precisely the original ambient Q-object and Q-arrow. -/
@[simp]
theorem auxiliaryToIsoStructured_forget (N : C) :
    auxiliaryToIsoStructured P N ⋙ isoStructuredInclusion P _ ⋙ StructuredArrow.proj _ (quotientMapQ
      P) =
      auxiliaryForgetQ P N := rfl

/-- A specified quotient identification gives the actual source identification
for each auxiliary object. -/
def auxiliaryQuotientObjIsoWithBase {N : C} {V : P.isoModSerre.Localization}
    (φ : P.isoModSerre.Q.obj N ≅ V) (X : AuxiliaryKernel P N) :
    (quotientMapQ P).obj ((auxiliaryForgetQ P N).obj X) ≅
      QConstruction.of ((abelianExactStructure P.isoModSerre.Localization)).deflation
        ((abelianExactStructure P.isoModSerre.Localization)).inflation V :=
  ((abelianExactStructure P.isoModSerre.Localization)).qIsoOfIso
    (asIso (P.isoModSerre.Q.map X.obj.obj.of.hom) ≪≫ φ)

lemma auxiliaryQuotientObjIsoWithBase_naturality {N : C} {V : P.isoModSerre.Localization}
    (φ : P.isoModSerre.Q.obj N ≅ V) {X Y : AuxiliaryKernel P N} (f : X ⟶ Y) :
    (quotientMapQ P).map ((auxiliaryForgetQ P N).map f) ≫
        (auxiliaryQuotientObjIsoWithBase P φ Y).hom =
      (auxiliaryQuotientObjIsoWithBase P φ X).hom := by
  change (quotientMapQ P).map ((auxiliaryForgetQ P N).map f) ≫
      QConstruction.inflationArrow (P.isoModSerre.Q.map Y.obj.obj.of.hom ≫ φ.hom) =
    QConstruction.inflationArrow (P.isoModSerre.Q.map X.obj.obj.of.hom ≫ φ.hom)
  rw [← QConstruction.inflationArrow_comp, ← QConstruction.inflationArrow_comp, ← Category.assoc]
  exact congrArg (· ≫ QConstruction.inflationArrow φ.hom) (auxiliaryQuotientObjIso_naturality P f)

/-- The comparison for an arbitrary chosen identification of the quotient base. -/
def auxiliaryToIsoStructuredWithBase {N : C} {V : P.isoModSerre.Localization}
    (φ : P.isoModSerre.Q.obj N ≅ V) :
    AuxiliaryKernel P N ⥤ IsoStructuredComma P
      (QConstruction.of ((abelianExactStructure P.isoModSerre.Localization)).deflation
        ((abelianExactStructure P.isoModSerre.Localization)).inflation V) where
  obj X := ⟨StructuredArrow.mk (Y := (auxiliaryForgetQ P N).obj X)
    (auxiliaryQuotientObjIsoWithBase P φ X).inv, by
      change IsIso (auxiliaryQuotientObjIsoWithBase P φ X).inv
      infer_instance⟩
  map f := ObjectProperty.homMk (StructuredArrow.homMk ((auxiliaryForgetQ P N).map f) (by
    apply (cancel_mono (auxiliaryQuotientObjIsoWithBase P φ _).hom).1
    simpa using congrArg ((auxiliaryQuotientObjIsoWithBase P φ _).inv ≫ ·)
      (auxiliaryQuotientObjIsoWithBase_naturality P φ f)))
  map_id X := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact (auxiliaryForgetQ P N).map_id X
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact (auxiliaryForgetQ P N).map_comp f g

@[simp]
theorem auxiliaryToIsoStructuredWithBase_forget {N : C} {V : P.isoModSerre.Localization}
    (φ : P.isoModSerre.Q.obj N ≅ V) :
    auxiliaryToIsoStructuredWithBase P φ ⋙ isoStructuredInclusion P _ ⋙
      StructuredArrow.proj _ (quotientMapQ P) = auxiliaryForgetQ P N := rfl

/-- Compatibility with a morphism between chosen ordinary quotient lifts is
an actual natural isomorphism with identity ambient components. -/
def auxiliaryToIsoStructuredWithBasePostcomposeIso {M N : C} {V : P.isoModSerre.Localization}
    (i : M ⟶ N) (hi : P.isoModSerre i)
    (φ : P.isoModSerre.Q.obj M ≅ V) (ψ : P.isoModSerre.Q.obj N ≅ V)
    (h : P.isoModSerre.Q.map i ≫ ψ.hom = φ.hom) :
    auxiliaryPostcompose P i hi ⋙ auxiliaryToIsoStructuredWithBase P ψ ≅
      auxiliaryToIsoStructuredWithBase P φ :=
  NatIso.ofComponents (fun X => ObjectProperty.isoMk _
    (StructuredArrow.isoMk (Iso.refl (QConstruction.of _ _ X.obj.obj.of.left)) (by
      change (auxiliaryQuotientObjIsoWithBase P ψ ((auxiliaryPostcompose P i hi).obj X)).inv ≫
        (quotientMapQ P).map (𝟙 ((auxiliaryForgetQ P M).obj X)) =
          (auxiliaryQuotientObjIsoWithBase P φ X).inv
      erw [(quotientMapQ P).map_id, Category.comp_id]
      have he : asIso (P.isoModSerre.Q.map (((auxiliaryPostcompose P i hi).obj X).obj.obj.of.hom))
        ≪≫ ψ =
          asIso (P.isoModSerre.Q.map X.obj.obj.of.hom) ≪≫ φ := by
        apply Iso.ext
        change P.isoModSerre.Q.map (X.obj.obj.of.hom ≫ i) ≫ ψ.hom =
          P.isoModSerre.Q.map X.obj.obj.of.hom ≫ φ.hom
        rw [Functor.map_comp, Category.assoc, h]
      exact congrArg (fun e => (((abelianExactStructure P.isoModSerre.Localization)).qIsoOfIso
        e).inv) he))) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    change (overForgetQ N).map ((overPostcomposeQ i).map f.hom) ≫ 𝟙 _ =
      𝟙 _ ≫ (overForgetQ M).map f.hom
    simp only [Category.comp_id, Category.id_comp]
    obtain ⟨s, hs⟩ := Quotient.exists_rep f.hom
    rw [← hs]
    rfl)

/-- The identity-component comparison is strict equality of functors,
providing the naturality equation of the filtered auxiliary cocone. -/
theorem auxiliaryToIsoStructuredWithBase_postcompose {M N : C} {V : P.isoModSerre.Localization}
    (i : M ⟶ N) (hi : P.isoModSerre i)
    (φ : P.isoModSerre.Q.obj M ≅ V) (ψ : P.isoModSerre.Q.obj N ≅ V)
    (h : P.isoModSerre.Q.map i ≫ ψ.hom = φ.hom) :
    auxiliaryPostcompose P i hi ⋙ auxiliaryToIsoStructuredWithBase P ψ =
      auxiliaryToIsoStructuredWithBase P φ := by
  let e := auxiliaryToIsoStructuredWithBasePostcomposeIso P i hi φ ψ h
  have he : ∀ X, (auxiliaryPostcompose P i hi ⋙ auxiliaryToIsoStructuredWithBase P ψ).obj X =
      (auxiliaryToIsoStructuredWithBase P φ).obj X := by
    intro X
    apply ObjectProperty.FullSubcategory.ext
    refine StructuredArrow.obj_ext
      ((auxiliaryPostcompose P i hi ⋙ auxiliaryToIsoStructuredWithBase P ψ).obj X).obj
      ((auxiliaryToIsoStructuredWithBase P φ).obj X).obj (by rfl) ?_
    exact StructuredArrow.w (e.app X).hom.hom
  refine CategoryTheory.Functor.ext he ?_
  intro X Y f
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom,
    StructuredArrow.comp_right, StructuredArrow.eqToHom_right]
  change (overForgetQ N).map ((overPostcomposeQ i).map f.hom) =
    𝟙 _ ≫ (overForgetQ M).map f.hom ≫ 𝟙 _
  simp only [Category.comp_id, Category.id_comp]
  obtain ⟨s, hs⟩ := Quotient.exists_rep f.hom
  rw [← hs]
  rfl

end CategoryTheory.ExactCategory.SerreLocalization
