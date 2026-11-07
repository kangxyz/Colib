/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExtensionLinear
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionProjection

/-!
# Original change of rings on the localized total extension category

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveExtensionBaseChange.lean`
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

/-- Both original coordinates respect the actual restricted diagonal action. -/
@[instance_reducible]
def rightBaseChangeExtensionPairLinear :
    letI := MonoidalLeftAction.restrictAlong
      (D := IsoCategory Sᵐᵒᵖ × (exactStructure Sᵐᵒᵖ).ExtensionTotal) (rightBaseChangeCore f)
    ((rightBaseChangeCore f).prod (rightBaseChangeExtension f)).LaxLeftLinear
      (IsoCategory Rᵐᵒᵖ) := by
  letI := MonoidalLeftAction.restrictAlong
    (D := (exactStructure Sᵐᵒᵖ).ExtensionTotal) (rightBaseChangeCore f)
  letI := rightBaseChangeExtensionLinear f
  letI := MonoidalLeftAction.restrictAlong
    (D := IsoCategory Sᵐᵒᵖ × (exactStructure Sᵐᵒᵖ).ExtensionTotal) (rightBaseChangeCore f)
  exact {
    μₗ := fun P x ↦ (Functor.LaxMonoidal.μ (rightBaseChangeCore f) P x.1,
      (rightBaseChangeExtensionTensorIso f P x.2).hom)
    μₗ_naturality_left := fun a x ↦ Prod.ext
      (Functor.LaxMonoidal.μ_natural_left (rightBaseChangeCore f) a x.1)
      (Functor.LaxLeftLinear.μₗ_naturality_left (rightBaseChangeExtension f) a x.2)
    μₗ_naturality_right := fun P _ _ a ↦ Prod.ext
      (Functor.LaxMonoidal.μ_natural_right (rightBaseChangeCore f) P a.1)
      (Functor.LaxLeftLinear.μₗ_naturality_right (rightBaseChangeExtension f) P a.2)
    μₗ_associativity := by
      intro P Q x
      apply Prod.ext
      · change Functor.LaxMonoidal.μ (rightBaseChangeCore f) (P ⊗ Q) x.1 ≫
          (rightBaseChangeCore f).map (α_ P Q x.1).hom =
          ((Functor.Monoidal.μIso (rightBaseChangeCore f) P Q).inv ▷
            (rightBaseChangeCore f).obj x.1 ≫
            (α_ ((rightBaseChangeCore f).obj P) ((rightBaseChangeCore f).obj Q)
              ((rightBaseChangeCore f).obj x.1)).hom) ≫
            (rightBaseChangeCore f).obj P ◁ Functor.LaxMonoidal.μ (rightBaseChangeCore f) Q x.1 ≫
              Functor.LaxMonoidal.μ (rightBaseChangeCore f) P (Q ⊗ x.1)
        have h := GroupCompletion.monoidalFunctor_action_associativity
          (rightBaseChangeCore f) P Q x.1
        simp only [Category.assoc] at h ⊢
        exact h
      · exact Functor.LaxLeftLinear.μₗ_associativity (rightBaseChangeExtension f) P Q x.2
    μₗ_unitality := fun x ↦ Prod.ext
      (GroupCompletion.monoidalFunctor_action_unitality (rightBaseChangeCore f) x.1)
      (Functor.LaxLeftLinear.μₗ_unitality (C := IsoCategory Rᵐᵒᵖ)
        (rightBaseChangeExtension f) x.2) }

/-- Change the actual denominator and extension by the original strong-monoidal base change. -/
def localizedExtensionBaseChange :
    LocalizedExtensionCategory Rᵐᵒᵖ ⥤ LocalizedExtensionCategory Sᵐᵒᵖ :=
  GroupCompletion.ActionLocalization.mapAlong (rightBaseChangeCore f)
    ((rightBaseChangeCore f).prod (rightBaseChangeExtension f))
    (rightBaseChangeExtensionPairLinear f)

/-- Both original object coordinates remain visible. -/
theorem localizedExtensionBaseChange_obj (A : IsoCategory Rᵐᵒᵖ)
    (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (localizedExtensionBaseChange f).obj (localizedExtensionPair Rᵐᵒᵖ A x) =
      localizedExtensionPair Sᵐᵒᵖ ((rightBaseChangeCore f).obj A)
        ((rightBaseChangeExtension f).obj x) := rfl

/-- The actual representative keeps the denominator, tensorator, and extension lineator. -/
theorem localizedExtensionBaseChange_mkHom
    {A B : IsoCategory Rᵐᵒᵖ} {x y : (exactStructure Rᵐᵒᵖ).ExtensionTotal}
    (P : IsoCategory Rᵐᵒᵖ) (a : P ⊗ A ⟶ B) (b : P ⊙ₗ x ⟶ y) :
    (localizedExtensionBaseChange f).map
      (GroupCompletion.Localization.mkHom (X := (A, x)) (Y := (B, y)) P a b) =
    GroupCompletion.Localization.mkHom
      (X := ((rightBaseChangeCore f).obj A, (rightBaseChangeExtension f).obj x))
      (Y := ((rightBaseChangeCore f).obj B, (rightBaseChangeExtension f).obj y))
      ((rightBaseChangeCore f).obj P)
      (Functor.LaxMonoidal.μ (rightBaseChangeCore f) P A ≫ (rightBaseChangeCore f).map a)
      ((rightBaseChangeExtensionTensorIso f P x).hom ≫ (rightBaseChangeExtension f).map b) := rfl

end ModuleCat.FiniteProjective
