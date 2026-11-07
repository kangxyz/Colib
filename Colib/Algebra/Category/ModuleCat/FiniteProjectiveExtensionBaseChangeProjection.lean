/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionBaseChange
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExtensionQuotient

/-!
# The original localized Q projection commutes with actual change of rings

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveExtensionBaseChangeProjection.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric inflationDirectSumAction
  rightBaseChangeMonoidal rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- Compatibility on each original translating extension representative. -/
theorem localizedExtensionBaseChangeProjection_mkHom
    {A B : IsoCategory Rᵐᵒᵖ} {x y : (exactStructure Rᵐᵒᵖ).ExtensionTotal}
    (P : IsoCategory Rᵐᵒᵖ) (a : P ⊗ A ⟶ B) (b : P ⊙ₗ x ⟶ y) :
    (rightBaseChangeExact f).mapQ.map
        ((localizedExtensionProjection Rᵐᵒᵖ).map
          (GroupCompletion.Localization.mkHom (X := (A, x)) (Y := (B, y)) P a b)) ≫
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso ((rightBaseChangeExact f).extensionQuotientIso y)).hom =
    ((exactStructure Sᵐᵒᵖ).qIsoOfIso ((rightBaseChangeExact f).extensionQuotientIso x)).hom ≫
      (localizedExtensionProjection Sᵐᵒᵖ).map
        ((localizedExtensionBaseChange f).map
          (GroupCompletion.Localization.mkHom (X := (A, x)) (Y := (B, y)) P a b)) := by
  rw [localizedExtensionProjection_map_mkHom, localizedExtensionBaseChange_mkHom,
    localizedExtensionProjection_map_mkHom, Functor.map_comp,
    CategoryTheory.ExactCategory.ExactStructure.extensionProjectionQMap_comp, Category.assoc]
  have hn := (rightBaseChangeExact f).extensionProjection_naturality b
  change (rightBaseChangeExact f).mapQ.map ((exactStructure Rᵐᵒᵖ).extensionProjectionQMap b) ≫
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso ((rightBaseChangeExact f).extensionQuotientIso y)).hom =
    ((exactStructure Sᵐᵒᵖ).qIsoOfIso
      ((rightBaseChangeExact f).extensionQuotientIso (P ⊙ₗ x))).hom ≫
      (exactStructure Sᵐᵒᵖ).extensionProjectionQMap ((rightBaseChangeExtension f).map b) at hn
  rw [hn, ← Category.assoc]
  have hl := congrArg (fun k ↦ k ≫
    (exactStructure Sᵐᵒᵖ).extensionProjectionQMap ((rightBaseChangeExtension f).map b))
      (rightBaseChangeExtensionProjection_lineator f P x)
  simp only [Category.assoc] at hl ⊢
  exact hl

/-- The genuine natural isomorphism of the original localized projection square. -/
def localizedExtensionBaseChangeProjectionIso :
    localizedExtensionProjection Rᵐᵒᵖ ⋙ (rightBaseChangeExact f).mapQ ≅
      localizedExtensionBaseChange f ⋙ localizedExtensionProjection Sᵐᵒᵖ :=
  NatIso.ofComponents
    (fun X ↦ (exactStructure Sᵐᵒᵖ).qIsoOfIso
      ((rightBaseChangeExact f).extensionQuotientIso X.obj.2)) (by
        rintro X Y ⟨a⟩
        exact localizedExtensionBaseChangeProjection_mkHom f a.denom a.map.1 a.map.2)

/-- The square retains the canonical quotient comparison at every actual object. -/
theorem localizedExtensionBaseChangeProjectionIso_hom_app
    (A : IsoCategory Rᵐᵒᵖ) (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (localizedExtensionBaseChangeProjectionIso f).hom.app (localizedExtensionPair Rᵐᵒᵖ A x) =
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso ((rightBaseChangeExact f).extensionQuotientIso x)).hom := rfl

end ModuleCat.FiniteProjective
