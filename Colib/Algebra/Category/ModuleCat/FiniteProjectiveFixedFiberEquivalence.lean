/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveDeflationEntry
public import Colib.CategoryTheory.GroupCompletion.LocalizationEquivalence
public import Colib.CategoryTheory.GroupCompletion.IsoFiber
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionProjection

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveFixedFiberEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Localized fixed-deflation fibers of the original Q projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Functor.LaxLeftLinear
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
attribute [local instance] extensionFiberDirectSumAction extensionIsoFiberDirectSumAction
attribute [local instance] extensionDeflationIsoFiberLinear extensionProjectionLinear

attribute [local instance] quotientTrivialAction quotientLineatorIsIso

/-- Localize the unchanged groupoid of deflations over the specified quotient. -/
abbrev LocalizedFixedExtensionCategory (C : Category.{u, u} R) :=
  GroupCompletion.Localization (IsoCategory R) ((exactStructure R).ExtensionFiber C)

/-- The generic fiber projection is exactly the previously constructed original-Q
projection, on objects and on the same denominator representatives. -/
lemma fiberProjection_eq_localizedExtensionProjection :
    GroupCompletion.Localization.fiberProjection (S := IsoCategory R)
      (exactStructure R).extensionProjection = localizedExtensionProjection R := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  obtain ⟨r, rfl⟩ := Quotient.exists_rep f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

/-- The identification retains the precise original arrow map. -/
lemma fiberProjection_map_eq {X Y : LocalizedExtensionCategory R} (f : X ⟶ Y) :
    (GroupCompletion.Localization.fiberProjection (S := IsoCategory R)
      (exactStructure R).extensionProjection).map f = (localizedExtensionProjection R).map f := by
  obtain ⟨r, rfl⟩ := Quotient.exists_rep f
  rfl

/-- Identify the two exactly equal projection presentations, retaining the
original total object, denominator, and specified base isomorphism. -/
def fixedFiberProjectionIdentification (C : Category.{u, u} R) :
    IsoFiber (GroupCompletion.Localization.fiberProjection (S := IsoCategory R)
      (exactStructure R).extensionProjection)
      (QConstruction.of (exactStructure R).deflation (exactStructure R).inflation C) ⥤
    IsoFiber (localizedExtensionProjection R)
      (QConstruction.of (exactStructure R).deflation (exactStructure R).inflation C) where
  obj X := IsoFiber.mk _ _ X.obj.right (asIso X.obj.hom)
  map {X Y} f := ⟨StructuredArrow.homMk f.hom.right (by
    change X.obj.hom ≫ (localizedExtensionProjection R).map f.hom.right = Y.obj.hom
    rw [← fiberProjection_map_eq]
    exact f.hom.w)⟩
  map_id X := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    rfl

/-- The projection identification reflects equality of the original underlying arrows. -/
instance fixedFiberProjectionIdentification_faithful (C : Category.{u, u} R) :
    (fixedFiberProjectionIdentification R C).Faithful where
  map_injective {_ _} f g h := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact congrArg (fun k ↦ k.hom.right) h

/-- Every arrow lifts through the exact equality of the two projection presentations. -/
instance fixedFiberProjectionIdentification_full (C : Category.{u, u} R) :
    (fixedFiberProjectionIdentification R C).Full where
  map_surjective f := by
    refine ⟨⟨StructuredArrow.homMk f.hom.right ?_⟩, ?_⟩
    · change _ ≫ (GroupCompletion.Localization.fiberProjection
        (exactStructure R).extensionProjection).map f.hom.right = _
      rw [fiberProjection_map_eq]
      exact f.hom.w
    · apply ObjectProperty.hom_ext
      apply StructuredArrow.hom_ext
      rfl

/-- Every original isomorphism-fiber object is retained up to its identity isomorphism. -/
instance fixedFiberProjectionIdentification_essSurj (C : Category.{u, u} R) :
    (fixedFiberProjectionIdentification R C).EssSurj where
  mem_essImage X := by
    let Y := IsoFiber.mk (GroupCompletion.Localization.fiberProjection (S := IsoCategory R)
      (exactStructure R).extensionProjection) _ X.obj.right (asIso X.obj.hom)
    refine ⟨Y, ⟨(isoFiberProperty (localizedExtensionProjection R) _).isoMk
      (StructuredArrow.isoMk (Iso.refl X.obj.right) ?_)⟩⟩
    change X.obj.hom ≫ (localizedExtensionProjection R).map (𝟙 X.obj.right) = X.obj.hom
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The original projection identification is an equivalence of the actual fibers. -/
instance fixedFiberProjectionIdentification_isEquivalence (C : Category.{u, u} R) :
    (fixedFiberProjectionIdentification R C).IsEquivalence where

/-- The actual localized fixed-deflation groupoid is the original localized
projection's isomorphism fiber at the prescribed original Q object. -/
def localizedFixedExtensionFiberEquivalence (C : Category.{u, u} R) :
    LocalizedFixedExtensionCategory R C ≌ IsoFiber (localizedExtensionProjection R)
      (QConstruction.of (exactStructure R).deflation (exactStructure R).inflation C) :=
  (GroupCompletion.Localization.mapEquivalence (C := IsoCategory R)
    ((exactStructure R).extensionDeflationIsoFiber C)).trans
    ((GroupCompletion.Localization.isoFiberEquivalence (S := IsoCategory R)
      (exactStructure R).extensionProjection _).trans
      (fixedFiberProjectionIdentification R C).asEquivalence)

end ModuleCat.FiniteProjective
