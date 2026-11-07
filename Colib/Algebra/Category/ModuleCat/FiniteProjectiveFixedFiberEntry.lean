/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveFixedFiberEquivalence

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveFixedFiberEntry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Original objects and arrows of the localized fixed-fiber entry -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
attribute [local instance] extensionFiberDirectSumAction extensionIsoFiberDirectSumAction
attribute [local instance] extensionDeflationEntryLinear extensionDeflationIsoFiberLinear
attribute [local instance] quotientTrivialAction quotientLineatorIsIso extensionProjectionLinear

/-- The actual fixed-fiber entry into the original structured-comma category. -/
def localizedFixedExtensionEntry (C : Category.{u, u} R) :
    LocalizedFixedExtensionCategory R C ⥤ StructuredArrow
      (QConstruction.of (exactStructure R).deflation (exactStructure R).inflation C)
      (localizedExtensionProjection R) :=
  (localizedFixedExtensionFiberEquivalence R C).functor ⋙
    IsoFiber.toStructured (localizedExtensionProjection R) _

/-- The original projective denominator and the chosen-kernel extension are retained. -/
@[simp]
lemma localizedFixedExtensionEntry_obj_right (C : Category.{u, u} R)
    (A : IsoCategory R) (p : (exactStructure R).ExtensionFiber C) :
    ((localizedFixedExtensionEntry R C).obj ⟨(A, p)⟩).right =
      localizedExtensionPair R A ((exactStructure R).extensionOfDeflation p.of) := rfl

/-- The specified structure map is the inverse of the original canonical quotient iso. -/
@[simp]
lemma localizedFixedExtensionEntry_obj_hom (C : Category.{u, u} R)
    (A : IsoCategory R) (p : (exactStructure R).ExtensionFiber C) :
    ((localizedFixedExtensionEntry R C).obj ⟨(A, p)⟩).hom =
      ((exactStructure R).qIsoOfIso
        ((exactStructure R).extensionOfDeflationQuotientIso p.of)).inv := rfl

/-- On an actual representative the entry retains its denominator and inserts
only the canonical identity-middle kernel comparison. -/
lemma localizedFixedExtensionEntry_map_mkHom (C : Category.{u, u} R)
    {A B : IsoCategory R} {p q : (exactStructure R).ExtensionFiber C}
    (S : IsoCategory R) (f : S ⊗ A ⟶ B) (g : S ⊙ₗ p ⟶ q) :
    ((localizedFixedExtensionEntry R C).map
      (GroupCompletion.Localization.mkHom (X := (A, p)) (Y := (B, q)) S f g)).right =
      GroupCompletion.Localization.mkHom
        (X := (A, (exactStructure R).extensionOfDeflation p.of))
        (Y := (B, (exactStructure R).extensionOfDeflation q.of)) S f
        ((extensionDeflationAddIso R C S p).hom ≫
          ((exactStructure R).extensionDeflationEntry C).map g) := by
  change ((GroupCompletion.Localization.isoFiberEntry
    (exactStructure R).extensionProjection _).map
      ((GroupCompletion.Localization.actedMapFunctor
        ((exactStructure R).extensionDeflationIsoFiber C)).map
          (GroupCompletion.Localization.mkHom (X := (A, p)) (Y := (B, q)) S f g))).hom.right = _
  rw [GroupCompletion.Localization.actedMapFunctor_mkHom]
  change (GroupCompletion.Localization.actedMapFunctor (IsoFiber.forget
    (exactStructure R).extensionProjection _)).map
      (GroupCompletion.Localization.mkHom
        (X := (A, ((exactStructure R).extensionDeflationIsoFiber C).obj p))
        (Y := (B, ((exactStructure R).extensionDeflationIsoFiber C).obj q)) S f _) = _
  rw [GroupCompletion.Localization.actedMapFunctor_mkHom]
  change GroupCompletion.Localization.mkHom
    (X := (A, (exactStructure R).extensionOfDeflation p.of))
    (Y := (B, (exactStructure R).extensionOfDeflation q.of)) S f (𝟙 _ ≫ _) = _
  rw [Category.id_comp]
  rfl

end ModuleCat.FiniteProjective
