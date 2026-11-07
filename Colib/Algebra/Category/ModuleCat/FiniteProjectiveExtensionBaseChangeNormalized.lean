/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionBaseChangeIdentityNaturality
public import Colib.CategoryTheory.ExactCategory.Functor.NormalizedQ

/-!
# The original extension square with the original strictly rebased Q functor

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveExtensionBaseChangeNormalized.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- The existing normalization isomorphism of the original Q base-change functor. -/
def rightBaseChangeQRebaseIso :
    (rightBaseChangeExact f).mapQ ≅ (rightBaseChangeExact f).normalizedQ :=
  rebaseFunctorIso (rightBaseChangeExact f).mapQ
    (exactStructure Rᵐᵒᵖ).qZero (exactStructure Sᵐᵒᵖ).qZero
    ((exactStructure Sᵐᵒᵖ).qIsoOfIso (rightBaseChange f).mapZeroObject)

/-- The exact object equality used to base the original Q-map. -/
theorem rightBaseChangeNormalizedZero :
    (rightBaseChangeExact f).normalizedQ.obj (exactStructure Rᵐᵒᵖ).qZero =
      (exactStructure Sᵐᵒᵖ).qZero :=
  rebaseFunctor_obj_base _ _ _ _

/-- The normalized zero component retains the supplied original Q zero-isomorphism. -/
lemma rightBaseChangeQRebaseIso_zero :
    (rightBaseChangeQRebaseIso f).hom.app (exactStructure Rᵐᵒᵖ).qZero ≫
      eqToHom (rightBaseChangeNormalizedZero f) =
        ((exactStructure Sᵐᵒᵖ).qIsoOfIso (rightBaseChange f).mapZeroObject).hom := by
  rw [show (rightBaseChangeQRebaseIso f).hom.app (exactStructure Rᵐᵒᵖ).qZero =
    ((exactStructure Sᵐᵒᵖ).qIsoOfIso (rightBaseChange f).mapZeroObject).hom ≫
      eqToHom (rightBaseChangeNormalizedZero f).symm from
        rebaseFunctorIso_hom_base _ _ _ _]
  simp

/-- The actual extension-projection square using precisely the Q functor underlying KMap. -/
def localizedExtensionBaseChangeNormalizedIso :
    localizedExtensionProjection Rᵐᵒᵖ ⋙ (rightBaseChangeExact f).normalizedQ ≅
      localizedExtensionBaseChange f ⋙ localizedExtensionProjection Sᵐᵒᵖ :=
  Functor.isoWhiskerLeft (localizedExtensionProjection Rᵐᵒᵖ)
    (rightBaseChangeQRebaseIso f).symm ≪≫ localizedExtensionBaseChangeProjectionIso f

/-- The normalized identity-entry triangle is the same original quotient triangle. -/
theorem completionIdentityBaseChangeNormalized_triangle (U : GroupCompletionCategory Rᵐᵒᵖ) :
    (localizedExtensionBaseChangeNormalizedIso f).hom.app
        ((completionIdentityEntry Rᵐᵒᵖ).obj U) ≫
      (localizedExtensionProjection Sᵐᵒᵖ).map
        ((completionIdentityBaseChangeNatIso f).hom.app U) ≫
      (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom.app ((completionBaseChange f).obj U) =
    (rightBaseChangeExact f).normalizedQ.map
        ((completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom.app U) ≫
      eqToHom (rightBaseChangeNormalizedZero f) := by
  apply (cancel_epi ((rightBaseChangeQRebaseIso f).hom.app
    ((localizedExtensionProjection Rᵐᵒᵖ).obj ((completionIdentityEntry Rᵐᵒᵖ).obj U)))).1
  change (rightBaseChangeQRebaseIso f).hom.app _ ≫
      (((rightBaseChangeQRebaseIso f).inv.app _ ≫
        (localizedExtensionBaseChangeProjectionIso f).hom.app _) ≫ _) = _
  rw [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [completionIdentityBaseChangeNatIso_zero_triangle]
  rw [← Category.assoc]
  rw [← (rightBaseChangeQRebaseIso f).hom.naturality]
  rw [Category.assoc]
  exact congrArg (fun k ↦
    (rightBaseChangeExact f).mapQ.map
      ((completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom.app U) ≫ k)
        (rightBaseChangeQRebaseIso_zero f).symm

end ModuleCat.FiniteProjective
