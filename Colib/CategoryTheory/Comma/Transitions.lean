/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Original comma transformations and transitions

The structure-arrow transformations, pre/postcomposition transitions and
their original projection, composition, opposite and natural-isomorphism
comparisons are categorical. The original common small-category universe
assumptions are retained; no classifying spaces or homotopy hypotheses occur.
-/
/-! Implementation source: `Quillen/Aglib/CategoryTheory/Comma/Transitions.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual comma categories, nerves and
path-space maps are retained; no fiber-equivalence conclusion is assumed. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Opposite
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The structure arrows of `(F ↓ d)` form the canonical transformation to `d`. -/
@[simps]
def commaTransformation (d : D) :
    CostructuredArrow.proj F d ⋙ F ⟶ (Functor.const (CostructuredArrow F d)).obj d where
  app X := X.hom
  naturality X Y f := by simp

/-- Postcomposition in the comma category, covariant in the target object. -/
abbrev transition {d e : D} (f : d ⟶ e) :
    CostructuredArrow F d ⥤ CostructuredArrow F e := CostructuredArrow.map f

/-- The postcomposition functor leaves the underlying source object unchanged. -/
@[simp]
theorem transition_projection {d e : D} (f : d ⟶ e) :
    transition F f ⋙ CostructuredArrow.proj F e = CostructuredArrow.proj F d := rfl

/-- The structure arrows in `(d ↓ F)`. -/
@[simps]
def structuredCommaTransformation (d : D) :
    (Functor.const (StructuredArrow d F)).obj d ⟶ StructuredArrow.proj d F ⋙ F where
  app X := X.hom
  naturality X Y f := by simp

/-- Precomposition is contravariant in the object defining the structured comma. -/
abbrev structuredTransition {d e : D} (f : d ⟶ e) :
    StructuredArrow e F ⥤ StructuredArrow d F := StructuredArrow.map f

@[simp] theorem structuredTransition_projection {d e : D} (f : d ⟶ e) :
    structuredTransition F f ⋙ StructuredArrow.proj d F = StructuredArrow.proj e F := rfl

/-- Opposite structured commas have exactly the correct costructured transitions. -/
theorem structuredOppositeTransition {d e : D} (f : d ⟶ e) :
    (structuredArrowOpEquivalence F e).functor ⋙ transition F.op f.op =
      (structuredTransition F f).op ⋙ (structuredArrowOpEquivalence F d).functor := by
  refine CategoryTheory.Functor.hext (fun X ↦ rfl) ?_
  intro X Y a
  rfl

lemma structuredTransition_comp_eq {d e z : D} (f : d ⟶ e) (g : e ⟶ z) :
    structuredTransition F (f ≫ g) = structuredTransition F g ⋙ structuredTransition F f := by
  refine CategoryTheory.Functor.ext (fun X => StructuredArrow.map_comp) ?_
  intro X Y h
  apply StructuredArrow.hom_ext
  simp only [StructuredArrow.comp_right, StructuredArrow.eqToHom_right,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl


end CategoryTheory.TheoremB

namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G : C ⥤ D}

/-- Changing the original functor commutes with comma postcomposition. -/
def commaIsoTransitionIso (e : F ≅ G) {d d' : D} (f : d ⟶ d') :
    (CostructuredArrow.mapNatIso (T := d) e).functor ⋙ transition G f ≅
      transition F f ⋙ (CostructuredArrow.mapNatIso (T := d') e).functor :=
  NatIso.ofComponents (fun X ↦ CostructuredArrow.isoMk (Iso.refl _)
    (by simp [transition])) (by
    intro X Y a
    apply CostructuredArrow.hom_ext
    simp)

/-- The natural isomorphism expressing compatibility of structured-comma transition along `f : d ⟶
d'` with transport across `e : F ≅ G`. -/
def structuredCommaIsoTransitionIso (e : F ≅ G) {d d' : D} (f : d ⟶ d') :
    (StructuredArrow.mapNatIso (S := d') e).functor ⋙ structuredTransition G f ≅
      structuredTransition F f ⋙ (StructuredArrow.mapNatIso (S := d) e).functor :=
  NatIso.ofComponents (fun X ↦ StructuredArrow.isoMk (Iso.refl _)
    (by simp [structuredTransition])) (by
    intro X Y a
    apply StructuredArrow.hom_ext
    simp)

end CategoryTheory.TheoremB
