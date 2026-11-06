/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Actual native restricted-span Q-arrows, comparison functors and realization maps are retained. -/

public import Colib.CategoryTheory.QConstruction.Abelian.InflationFaithful
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryArrowLift
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryDiagram
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-! # Faithfulness and eventual equality of auxiliary object lifts -/
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
variable (P : ObjectProperty C) [P.IsSerreClass]

instance auxiliaryForgetQ_faithful (N : C) : (auxiliaryForgetQ P N).Faithful := by
  dsimp [auxiliaryForgetQ]
  infer_instance

/-- Each comparison leg is faithful before taking the filtered colimit. -/
instance auxiliaryToIsoStructuredWithBase_faithful {N : C} {V : P.isoModSerre.Localization}
    (φ : P.isoModSerre.Q.obj N ≅ V) : (auxiliaryToIsoStructuredWithBase P φ).Faithful where
  map_injective := by
    intro X Y f g h
    apply (auxiliaryForgetQ P N).map_injective
    exact congrArg (fun k => k.hom.right) h

/-- Equal comparison objects on the same ambient source have equal
localized ordinary structure maps. -/
lemma auxiliaryOverMk_map_eq_of_comparison_eq {N S : C} {V : P.isoModSerre.Localization}
    (φ : P.isoModSerre.Q.obj N ≅ V) (f g : S ⟶ N)
    (hf : P.isoModSerre f) (hg : P.isoModSerre g)
    (h : (auxiliaryToIsoStructuredWithBase P φ).obj (auxiliaryOverMk P f hf) =
      (auxiliaryToIsoStructuredWithBase P φ).obj (auxiliaryOverMk P g hg)) :
    P.isoModSerre.Q.map f = P.isoModSerre.Q.map g := by
  let a := auxiliaryQuotientObjIsoWithBase P φ (auxiliaryOverMk P f hf)
  let b := auxiliaryQuotientObjIsoWithBase P φ (auxiliaryOverMk P g hg)
  have hinv : a.inv = b.inv := by
    have hh := StructuredArrow.w (eqToHom h).hom
    simp only [ObjectProperty.eqToHom_hom, StructuredArrow.eqToHom_right, eqToHom_refl] at hh
    erw [(quotientMapQ P).map_id, Category.comp_id] at hh
    exact hh
  have hhom := (Iso.inv_eq_inv a b).1 hinv
  have : IsIso (P.isoModSerre.Q.map f) := Localization.inverts _ _ _ hf
  have : IsIso (P.isoModSerre.Q.map g) := Localization.inverts _ _ _ hg
  change QConstruction.inflationArrow (P.isoModSerre.Q.map f ≫ φ.hom) =
    QConstruction.inflationArrow (P.isoModSerre.Q.map g ≫ φ.hom) at hhom
  exact (cancel_mono φ.hom).1 (QConstruction.inflationArrow_injective _ _ hhom)

/-- Objects identified by one comparison leg become literally equal after
one Serre-isomorphic postcomposition. The denominator is supplied by the
proved calculus of fractions. -/
theorem auxiliary_eventual_obj_eq {N : C} {V : P.isoModSerre.Localization}
    (φ : P.isoModSerre.Q.obj N ≅ V) (X Y : AuxiliaryKernel P N)
    (h : (auxiliaryToIsoStructuredWithBase P φ).obj X =
      (auxiliaryToIsoStructuredWithBase P φ).obj Y) :
    ∃ (M : C) (s : N ⟶ M) (hs : P.isoModSerre s),
      (auxiliaryPostcompose P s hs).obj X = (auxiliaryPostcompose P s hs).obj Y := by
  rcases X with ⟨⟨⟨X⟩⟩, hX⟩
  rcases Y with ⟨⟨⟨Y⟩⟩, hY⟩
  obtain ⟨S, f, rfl⟩ := Over.mk_surjective X
  obtain ⟨T, g, rfl⟩ := Over.mk_surjective Y
  have hST : S = T := congrArg (fun A => A.obj.right.obj.of) h
  subst T
  have heq := auxiliaryOverMk_map_eq_of_comparison_eq P φ f g hX hY h
  obtain ⟨M, s, hs, hfg⟩ := (MorphismProperty.map_eq_iff_postcomp
    P.isoModSerre.Q P.isoModSerre f g).1 heq
  refine ⟨M, s, hs, ?_⟩
  apply ObjectProperty.FullSubcategory.ext
  change QConstruction.of _ _ (Over.mk (f ≫ s)) = QConstruction.of _ _ (Over.mk (g ≫ s))
  rw [hfg]

/-- A denominator refinement is itself a morphism of ordinary quotient
lifts, so the previous equality holds at a genuine later diagram stage. -/
theorem quotientAuxiliaryLift_eventual_obj_eq {V : P.isoModSerre.Localization}
    (A : QuotientAuxiliaryLift P V) (X Y : AuxiliaryKernel P A.obj.left)
    (h : (auxiliaryToIsoStructuredWithBase P (asIso A.obj.hom)).obj X =
      (auxiliaryToIsoStructuredWithBase P (asIso A.obj.hom)).obj Y) :
    ∃ (B : QuotientAuxiliaryLift P V) (s : A ⟶ B),
      (auxiliaryPostcompose P s.hom.left
        (auxiliaryLift_hom_isoModSerre P.isoModSerre.Q V P s)).obj X =
      (auxiliaryPostcompose P s.hom.left
        (auxiliaryLift_hom_isoModSerre P.isoModSerre.Q V P s)).obj Y := by
  obtain ⟨M, s, hs, heq⟩ := auxiliary_eventual_obj_eq P (asIso A.obj.hom) X Y h
  have : IsIso (P.isoModSerre.Q.map s) := Localization.inverts _ _ _ hs
  let e : P.isoModSerre.Q.obj M ≅ V := (asIso (P.isoModSerre.Q.map s)).symm ≪≫ asIso A.obj.hom
  let B : QuotientAuxiliaryLift P V := auxiliaryLiftMk P.isoModSerre.Q V e
  let t : A ⟶ B := ObjectProperty.homMk (CostructuredArrow.homMk s (by simp [B, e,
    auxiliaryLiftMk]))
  exact ⟨B, t, heq⟩

end CategoryTheory.ExactCategory.SerreLocalization
