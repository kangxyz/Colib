/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryColimit

/-! # Regression contracts for the genuine Serre auxiliary colimit

The tests exercise actual ordinary arrows, native Q-spans, literal refinement,
strict diagram composition, and the colimit universal property. No homotopy
comparison or colimit conclusion is provided as a hypothesis.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂ u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.ExactCategory.SerreLocalization CategoryTheory.Localization

-- Generic owners retain independent universes.
example {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {W V : MorphismProperty C} {W' V' : MorphismProperty D}
    (F G : QConstruction.CompatibleFunctor W V W' V')
    (h : F.toFunctor = G.toFunctor) : F = G :=
  QConstruction.CompatibleFunctor.ext_toFunctor h

example {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {P : ObjectProperty D} (F G : C ⥤ P.FullSubcategory)
    (h : F ⋙ P.ι = G ⋙ P.ι) : F = G :=
  Functor.ext_of_comp_fullSubcategory h

example {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {X Y : C} (f g : X ⟶ Y) [Mono f] [Mono g]
    (h : QConstruction.inflationArrow f = QConstruction.inflationArrow g) : f = g :=
  QConstruction.inflationArrow_injective f g h

attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

-- The exact old Q-arrow, not merely an isomorphic or equivalent arrow, is retained.
example {X Y : C} (s : QConstruction.AbelianSpan X Y)
    (hl : P.isoModSerre s.l) (hr : P.isoModSerre s.r) :
    (auxiliaryForgetQ P (pushout s.l s.r)).map (auxiliarySpanLift P s hl hr) =
      QConstruction.mkHom _ _ s :=
  auxiliarySpanLift_forget P s hl hr

example {M N : C} (i : M ⟶ N) (hi : P.isoModSerre i) :
    (auxiliaryPostcomposeClassifyingHomotopyEquiv P i hi).toFun =
      (classifyingSpaceMap (auxiliaryPostcompose P i hi)).hom :=
  auxiliaryPostcomposeClassifyingHomotopyEquiv_toFun P i hi

example {M N R : C} (f : M ⟶ N) (g : N ⟶ R)
    (hf : P.isoModSerre f) (hg : P.isoModSerre g) :
    auxiliaryPostcompose P (f ≫ g) (P.isoModSerre.comp_mem f g hf hg) =
      auxiliaryPostcompose P f hf ⋙ auxiliaryPostcompose P g hg :=
  auxiliaryPostcompose_comp P f g hf hg

example (N : C) : auxiliaryPostcompose P (𝟙 N) (P.isoModSerre.id_mem N) =
    𝟭 (AuxiliaryKernel P N) := auxiliaryPostcompose_id P N

variable (V : P.isoModSerre.Localization)

example : IsFiltered (QuotientAuxiliaryLift P V) := inferInstance

-- A genuine denominator, not an assumed common-stage comparison, clears equality.
example {N : C} (φ : P.isoModSerre.Q.obj N ≅ V) (X Y : AuxiliaryKernel P N)
    (h : (auxiliaryToIsoStructuredWithBase P φ).obj X =
      (auxiliaryToIsoStructuredWithBase P φ).obj Y) :
    ∃ (M : C) (s : N ⟶ M) (hs : P.isoModSerre s),
      (auxiliaryPostcompose P s hs).obj X = (auxiliaryPostcompose P s hs).obj Y :=
  auxiliary_eventual_obj_eq P φ X Y h

-- Whole-arrow lifting retains both endpoints and the exact triangle.
example {A B : (quotientAuxiliaryCocone P V).pt} (f : A ⟶ B) :
    ∃ (j : QuotientAuxiliaryLift P V)
      (x y : (quotientAuxiliaryDiagram P V).obj j) (g : x ⟶ y)
      (hx : ((quotientAuxiliaryCocone P V).ι.app j).toFunctor.obj x = A)
      (hy : ((quotientAuxiliaryCocone P V).ι.app j).toFunctor.obj y = B),
      ((quotientAuxiliaryCocone P V).ι.app j).toFunctor.map g ≫ eqToHom hy =
        eqToHom hx ≫ f :=
  quotientAuxiliaryCocone_arrowSurjective P V f

-- The realized transition is the actual nerve transition.
example {A B : QuotientAuxiliaryLift P V} (f : A ⟶ B) :
    (quotientAuxiliaryNerveTransitionEquiv P V f).toFun =
      (SSet.toTop.map ((quotientAuxiliaryNerveDiagram P V).map f)).hom :=
  quotientAuxiliaryNerveTransitionEquiv_toFun P V f

-- The colimit vertex is the nerve of the actual isomorphism structured comma.
example : (quotientAuxiliaryNerveCocone P V).pt =
    nerve (IsoStructuredComma P (QConstruction.of
      (abelianExactStructure P.isoModSerre.Localization).deflation
      (abelianExactStructure P.isoModSerre.Localization).inflation V)) := rfl

-- Existence and uniqueness of descent follow from the proved universal property.
example (s : Cocone (quotientAuxiliaryNerveDiagram P V)) (A : QuotientAuxiliaryLift P V) :
    (quotientAuxiliaryNerveCocone P V).ι.app A ≫
      (quotientAuxiliaryNerveCoconeIsColimit P V).desc s = s.ι.app A :=
  (quotientAuxiliaryNerveCoconeIsColimit P V).fac s A

example (T : SSet.{u}) (f g : (quotientAuxiliaryNerveCocone P V).pt ⟶ T)
    (h : ∀ A, (quotientAuxiliaryNerveCocone P V).ι.app A ≫ f =
      (quotientAuxiliaryNerveCocone P V).ι.app A ≫ g) : f = g :=
  (quotientAuxiliaryNerveCoconeIsColimit P V).hom_ext h
