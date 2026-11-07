/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Actual native restricted-span Q-arrows, comparison functors and realization maps are retained. -/

public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryDiagram
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryArrowLift
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryRefinement
public import Colib.Topology.FilteredRealization.NerveColimit
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-! # The isomorphism structured comma as a filtered nerve colimit -/
@[expose] public section

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
  (P : ObjectProperty C) [P.IsSerreClass] (V : P.isoModSerre.Localization)

/-- The actual diagram of stage nerves. -/
def quotientAuxiliaryNerveDiagram : QuotientAuxiliaryLift P V ⥤ SSet.{u} :=
  quotientAuxiliaryDiagram P V ⋙ nerveFunctor

/-- Its canonical cocone targets the nerve of the actual isomorphism comma. -/
def quotientAuxiliaryNerveCocone : Cocone (quotientAuxiliaryNerveDiagram P V) :=
  nerveFunctor.mapCocone (quotientAuxiliaryCocone P V)

@[simp]
lemma quotientAuxiliaryCocone_lift (N : C) (φ : P.isoModSerre.Q.obj N ≅ V) :
    ((quotientAuxiliaryCocone P V).ι.app (auxiliaryLiftMk P.isoModSerre.Q V φ)).toFunctor =
      auxiliaryToIsoStructuredWithBase P φ := by
  change auxiliaryToIsoStructuredWithBase P (asIso φ.hom) = _
  congr 1
  apply Iso.ext
  rfl

/-- A whole comma arrow, including both endpoint equalities, lifts at one stage. -/
theorem quotientAuxiliaryCocone_arrowSurjective :
    FilteredNerveColimit.ArrowSurjective (quotientAuxiliaryDiagram P V) (quotientAuxiliaryCocone
        P V) := by
  intro X Y f
  obtain ⟨N, φ, A, B, g, hA, hB, hg⟩ := exists_isoStructured_arrow_lift P f
  let j := auxiliaryLiftMk P.isoModSerre.Q V φ
  have hleg : FilteredNerveColimit.leg (quotientAuxiliaryDiagram P V) (quotientAuxiliaryCocone P
      V) j =
      auxiliaryToIsoStructuredWithBase P φ := quotientAuxiliaryCocone_lift P V N φ
  refine ⟨j, A, B, g, ?_, ?_, ?_⟩
  · rw [hleg]
    exact hA
  · rw [hleg]
    exact hB
  · rw [Functor.congr_hom hleg g]
    simp only [Category.assoc, eqToHom_trans]
    have hh := congrArg (eqToHom (Functor.congr_obj hleg A) ≫ ·) hg
    simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using hh

/-- In particular, the cocone is jointly surjective on actual objects. -/
theorem quotientAuxiliaryCocone_objectSurjective :
    ∀ X : (quotientAuxiliaryCocone P V).pt,
      ∃ (j : QuotientAuxiliaryLift P V) (x : (quotientAuxiliaryDiagram P V).obj j),
        ((quotientAuxiliaryCocone P V).ι.app j).toFunctor.obj x = X := by
  intro X
  obtain ⟨j, x, _, _, hx, _, _⟩ := quotientAuxiliaryCocone_arrowSurjective P V (𝟙 X)
  exact ⟨j, x, hx⟩


/-- Equality of stage objects in the isomorphism comma is cleared by an
actual later ordinary Serre-isomorphic base. -/
theorem quotientAuxiliaryCocone_eventuallyEqualObjects :
    FilteredNerveColimit.EventuallyEqualObjects (quotientAuxiliaryDiagram P V)
      (quotientAuxiliaryCocone P V) := by
  intro A X Y h
  exact quotientAuxiliaryLift_eventual_obj_eq P A X Y h

instance quotientAuxiliaryCocone_faithful (A : QuotientAuxiliaryLift P V) :
    (FilteredNerveColimit.leg (quotientAuxiliaryDiagram P V) (quotientAuxiliaryCocone P V)
        A).Faithful :=
  auxiliaryToIsoStructuredWithBase_faithful P (asIso A.obj.hom)

/-- The nerve of the actual isomorphism comma is the filtered colimit of
the auxiliary nerves. Every finite chain and every equality was lifted above;
this is an actual universal property, not an assumed comparison. -/
def quotientAuxiliaryNerveCoconeIsColimit : IsColimit (quotientAuxiliaryNerveCocone P V) :=
  FilteredNerveColimit.nerveCoconeIsColimit (quotientAuxiliaryDiagram P V)
    (quotientAuxiliaryCocone P V) (quotientAuxiliaryCocone_objectSurjective P V)
    (quotientAuxiliaryCocone_arrowSurjective P V)
    (quotientAuxiliaryCocone_eventuallyEqualObjects P V)


/-- Each realized simplicial transition is exactly the proved auxiliary
postcomposition homotopy equivalence. -/
def quotientAuxiliaryNerveTransitionEquiv
    {A B : QuotientAuxiliaryLift P V} (f : A ⟶ B) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj ((quotientAuxiliaryNerveDiagram P V).obj A))
      (SSet.toTop.obj ((quotientAuxiliaryNerveDiagram P V).obj B)) :=
  quotientAuxiliaryTransitionHomotopyEquiv P f

@[simp]
theorem quotientAuxiliaryNerveTransitionEquiv_toFun
    {A B : QuotientAuxiliaryLift P V} (f : A ⟶ B) :
    (quotientAuxiliaryNerveTransitionEquiv P V f).toFun =
      (SSet.toTop.map ((quotientAuxiliaryNerveDiagram P V).map f)).hom := rfl

@[simp]
theorem quotientAuxiliaryNerveCocone_map (A : QuotientAuxiliaryLift P V) :
    SSet.toTop.map ((quotientAuxiliaryNerveCocone P V).ι.app A) =
      classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P (asIso A.obj.hom)) := rfl


/-- The structured lift retains the original isomorphism. -/
@[simp] theorem asIso_auxiliaryLiftMk (N : C) (φ : P.isoModSerre.Q.obj N ≅ V) :
    asIso (auxiliaryLiftMk P.isoModSerre.Q V φ).obj.hom = φ := by
  apply Iso.ext
  rfl


end CategoryTheory.ExactCategory.SerreLocalization
