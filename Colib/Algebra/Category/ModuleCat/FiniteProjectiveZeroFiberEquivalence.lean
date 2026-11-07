/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveZeroFiberEntry
public import Colib.CategoryTheory.ExactCategory.ExtensionZeroQuotient

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveZeroFiberEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The actual zero isomorphism fiber is the original projective group completion

A quotient isomorphic to zero in Q is zero in the original exact category.
Its inflation is therefore invertible by its kernel universal property. This
recovers the numerator module and yields essential surjectivity of the actual
identity-extension entry, which was already shown fully faithful.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
  extensionDirectSumAction identityExtensionLinear identityExtensionPairLinear

/-- Every object of the zero isomorphism fiber is isomorphic to an identity extension. -/
instance completionZeroIsoFiberEntry_essSurj : (completionZeroIsoFiberEntry R).EssSurj where
  mem_essImage U := by
    let A := U.obj.right.obj.1
    let x := U.obj.right.obj.2
    have hx : Limits.IsZero ((exactStructure R).extensionQuotientData x).obj :=
      (exactStructure R).isZero_of_qHom_to_zero _ (inv U.obj.hom)
    let B : IsoCategory R := ⟨x.fiber.unop.left.obj⟩
    let e : (completionIdentityEntry R).obj (completionPair R A B) ≅ U.obj.right :=
      (GroupCompletion.ActionLocalization.ofFunctor (C := IsoCategory R)
        (D := IsoCategory R × (exactStructure R).ExtensionTotal)).mapIso
          ((Iso.refl A).prod ((exactStructure R).identityExtensionIsoOfZeroQuotient x hx))
    refine ⟨completionPair R A B, ⟨(isoFiberProperty
      (localizedExtensionProjection R) (exactStructure R).qZero).isoMk ?_⟩⟩
    refine StructuredArrow.isoMk e ?_
    exact ((exactStructure R).qHom_subsingleton_of_isZero _ _ hx).elim _ _

instance completionZeroIsoFiberEntry_isEquivalence :
    (completionZeroIsoFiberEntry R).IsEquivalence where

/-- The equivalence retains the original identity-extension functor as its forward map. -/
def completionZeroIsoFiberEquivalence : GroupCompletionCategory R ≌ ZeroIsoFiber R :=
  (completionZeroIsoFiberEntry R).asEquivalence

@[simp]
lemma completionZeroIsoFiberEquivalence_functor :
    (completionZeroIsoFiberEquivalence R).functor = completionZeroIsoFiberEntry R := rfl

end ModuleCat.FiniteProjective
