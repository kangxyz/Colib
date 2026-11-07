/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionBaseChangeNormalized
public import Colib.CategoryTheory.TheoremB.NaturalTransformationFiberLift

/-!
# The actual normalized completion nullhomotopy square

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionBaseChangeNullhomotopy.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology SSet HomotopyGroup
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace CategoryTheory

/-- Transporting only the terminal functor preserves the entire realization homotopy. -/
theorem classifyingHomotopy_comp_eqToHom {A D : Type u}
    [SmallCategory A] [SmallCategory D] {P Q Q' : A ⥤ D}
    (α : P ⟶ Q) (h : Q = Q') (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (α ≫ eqToHom h) (t, x) =
      classifyingSpaceNaturalTransformationHomotopy α (t, x) := by
  subst Q'
  simp

end CategoryTheory

namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- The original normalized Q functor sends the constant zero functor to constant zero. -/
theorem completionBaseChangeConstantZero :
    (Functor.const (GroupCompletionCategory Rᵐᵒᵖ)).obj (exactStructure Rᵐᵒᵖ).qZero ⋙
        (rightBaseChangeExact f).normalizedQ =
      (Functor.const (GroupCompletionCategory Rᵐᵒᵖ)).obj (exactStructure Sᵐᵒᵖ).qZero := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rightBaseChangeNormalizedZero f)

/-- The target nullhomotopy after the actual identity-entry base-change transformation. -/
def completionBaseChangeTargetTransformation :
    completionIdentityEntry Rᵐᵒᵖ ⋙ localizedExtensionBaseChange f ⋙
        localizedExtensionProjection Sᵐᵒᵖ ⟶
      (Functor.const (GroupCompletionCategory Rᵐᵒᵖ)).obj (exactStructure Sᵐᵒᵖ).qZero :=
  Functor.whiskerRight (completionIdentityBaseChangeNatIso f).hom
      (localizedExtensionProjection Sᵐᵒᵖ) ≫
    Functor.whiskerLeft (completionBaseChange f)
      (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom

/-- The original normalized projection triangle holds as an equality of transformations. -/
theorem completionBaseChangeNullhomotopyTransformation :
    Functor.whiskerLeft (completionIdentityEntry Rᵐᵒᵖ)
        (localizedExtensionBaseChangeNormalizedIso f).hom ≫
      completionBaseChangeTargetTransformation f =
    Functor.whiskerRight (completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom
        (rightBaseChangeExact f).normalizedQ ≫
      eqToHom (completionBaseChangeConstantZero f) := by
  ext U
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, completionBaseChangeTargetTransformation,
    eqToHom_app] using completionIdentityBaseChangeNormalized_triangle f U

/-- At every point and time the composite triangle is the original mapped nullhomotopy. -/
theorem completionBaseChangeNullhomotopy_apply
    (t : unitInterval) (x : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    classifyingSpaceNaturalTransformationHomotopy
      (Functor.whiskerLeft (completionIdentityEntry Rᵐᵒᵖ)
          (localizedExtensionBaseChangeNormalizedIso f).hom ≫
        completionBaseChangeTargetTransformation f) (t, x) =
      classifyingSpaceMap (rightBaseChangeExact f).normalizedQ
        (classifyingSpaceNaturalTransformationHomotopy
          (completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom (t, x)) := by
  rw [completionBaseChangeNullhomotopyTransformation, classifyingHomotopy_comp_eqToHom,
    classifyingSpaceNaturalTransformationHomotopy_whiskerRight]

end ModuleCat.FiniteProjective
