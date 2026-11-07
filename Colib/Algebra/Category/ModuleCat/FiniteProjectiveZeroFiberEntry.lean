/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveIdentityExtension
public import Colib.KTheory.Plus.ProjectiveGroupCompletion
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionProjection
public import Colib.CategoryTheory.GroupCompletion.FullyFaithful

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveZeroFiberEntry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The original group completion enters the zero isomorphism fiber

The map sends `(A,B)` to `(A, id_B)`. Its projected quotient is compared to
zero by the canonical identity-cokernel isomorphism, retained as part of the
isomorphism-fiber object.
-/

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
  extensionDirectSumAction identityExtensionLinear

/-- Retain the denominator and replace the numerator by its identity extension. -/
def identityExtensionPairFunctor : IsoCategory R × IsoCategory R ⥤
    IsoCategory R × (exactStructure R).ExtensionTotal :=
  (𝟭 (IsoCategory R)).prod (exactStructure R).identityExtensionFunctor

/-- The identity-extension pair functor respects simultaneous direct-sum translation. -/
@[instance_reducible]
def identityExtensionPairLinear :
    (identityExtensionPairFunctor R).LaxLeftLinear (IsoCategory R) where
  μₗ S X := (𝟙 _, identityExtensionLineator R S X.2)
  μₗ_naturality_left f X := by
    apply Prod.ext
    · change f ▷ X.1 ≫ 𝟙 _ = 𝟙 _ ≫ f ▷ X.1
      simp
    · exact Functor.LaxLeftLinear.μₗ_naturality_left
        (exactStructure R).identityExtensionFunctor f X.2
  μₗ_naturality_right S _ _ f := by
    apply Prod.ext
    · change S ◁ f.1 ≫ 𝟙 _ = 𝟙 _ ≫ S ◁ f.1
      simp
    · exact Functor.LaxLeftLinear.μₗ_naturality_right
        (exactStructure R).identityExtensionFunctor S f.2
  μₗ_associativity S T X := by
    apply Prod.ext
    · change 𝟙 _ ≫ (α_ S T X.1).hom = (α_ S T X.1).hom ≫ S ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · exact Functor.LaxLeftLinear.μₗ_associativity
        (exactStructure R).identityExtensionFunctor S T X.2
  μₗ_unitality X := by
    apply Prod.ext
    · change (λ_ X.1).hom = 𝟙 _ ≫ (λ_ X.1).hom
      simp
    · exact Functor.LaxLeftLinear.μₗ_unitality
        (exactStructure R).identityExtensionFunctor X.2

attribute [local instance] identityExtensionPairLinear

instance identityExtensionPairFunctor_faithful : (identityExtensionPairFunctor R).Faithful where
  map_injective {_ _} f g h := by
    change (f.1, (exactStructure R).identityExtensionFunctor.map f.2) =
      (g.1, (exactStructure R).identityExtensionFunctor.map g.2) at h
    apply Prod.ext
    · have h1 := congrArg (fun z ↦ z.1) h
      exact h1
    · exact (exactStructure R).identityExtensionFunctor.map_injective (congrArg _root_.Prod.snd h)

instance identityExtensionPairFunctor_full : (identityExtensionPairFunctor R).Full where
  map_surjective f := by
    refine ⟨(f.1, (exactStructure R).identityExtensionFunctor.preimage f.2), ?_⟩
    change (f.1, (exactStructure R).identityExtensionFunctor.map
      ((exactStructure R).identityExtensionFunctor.preimage f.2)) = f
    apply Prod.ext
    · rfl
    · exact (exactStructure R).identityExtensionFunctor.map_preimage _

instance identityExtensionPairLineator_isIso (S : IsoCategory R)
    (X : IsoCategory R × IsoCategory R) :
    IsIso (Functor.LaxLeftLinear.μₗ (identityExtensionPairFunctor R) S X) :=
  inferInstanceAs (IsIso ((Iso.refl (S ⊗ X.1)).prod
    (identityExtensionLineatorIso R S X.2)).hom)

/-- The actual identity-extension entry descends to the existing quotient category. -/
def completionIdentityEntry : GroupCompletionCategory R ⥤ LocalizedExtensionCategory R :=
  GroupCompletion.ActionLocalization.mapFunctor (identityExtensionPairFunctor R)

instance completionIdentityEntry_faithful : (completionIdentityEntry R).Faithful :=
  inferInstanceAs ((GroupCompletion.ActionLocalization.mapFunctor
    (identityExtensionPairFunctor R)).Faithful)

instance completionIdentityEntry_full : (completionIdentityEntry R).Full :=
  inferInstanceAs ((GroupCompletion.ActionLocalization.mapFunctor
    (identityExtensionPairFunctor R)).Full)

@[simp]
lemma completionIdentityEntry_obj (A B : IsoCategory R) :
    (completionIdentityEntry R).obj (completionPair R A B) =
      localizedExtensionPair R A ((exactStructure R).identityExtension B.of) := rfl

/-- The chosen quotient of each identity extension is canonically zero, naturally
also on all localization morphisms. -/
def completionIdentityProjectionIsoZero :
    completionIdentityEntry R ⋙ localizedExtensionProjection R ≅
      (Functor.const (GroupCompletionCategory R)).obj (exactStructure R).qZero :=
  NatIso.ofComponents
    (fun X ↦ (exactStructure R).identityExtensionZeroIso X.obj.2)
    (fun _ ↦ ((exactStructure R).qHom_subsingleton_of_isZero _ _
      (Limits.isZero_zero (Category R))).elim _ _)

/-- The zero fiber stores isomorphisms, rather than fictitious equalities of chosen quotients. -/
abbrev ZeroIsoFiber :=
  IsoFiber (localizedExtensionProjection R) (exactStructure R).qZero

/-- The original `S⁻¹S` maps to the zero isomorphism fiber by actual identity extensions. -/
def completionZeroIsoFiberEntry : GroupCompletionCategory R ⥤ ZeroIsoFiber R :=
  IsoFiber.lift (localizedExtensionProjection R) (exactStructure R).qZero
    (completionIdentityEntry R) (completionIdentityProjectionIsoZero R).symm

instance completionZeroIsoFiberEntry_faithful : (completionZeroIsoFiberEntry R).Faithful :=
  inferInstanceAs ((IsoFiber.lift (localizedExtensionProjection R) (exactStructure R).qZero
    (completionIdentityEntry R) (completionIdentityProjectionIsoZero R).symm).Faithful)

instance completionZeroIsoFiberEntry_full : (completionZeroIsoFiberEntry R).Full :=
  inferInstanceAs ((IsoFiber.lift (localizedExtensionProjection R) (exactStructure R).qZero
    (completionIdentityEntry R) (completionIdentityProjectionIsoZero R).symm).Full)

end ModuleCat.FiniteProjective
