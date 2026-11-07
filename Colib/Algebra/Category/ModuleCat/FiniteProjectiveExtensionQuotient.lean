/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveInflationAction
public import Colib.CategoryTheory.Limits.Shapes.CoproductCokernel

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionQuotient.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Direct-sum invariance of extension quotients

Adding the same projective summand to kernel and middle object leaves the
quotient canonically isomorphic to the original quotient. The isomorphism
is derived from actual cokernel universal properties.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction

/-- Add a summand to both kernel and middle object of the actual total extension. -/
def directSumExtensionObject (S : IsoCategory R) (x : (exactStructure R).ExtensionTotal) :
    (exactStructure R).ExtensionTotal :=
  Subdivision.of (S ⊴ₗ x.fiber.unop.hom)

/-- The quotient of the direct-sum extension is canonically the original quotient. -/
def directSumExtensionQuotientIso (S : IsoCategory R) (x : (exactStructure R).ExtensionTotal) :
    ((exactStructure R).extensionQuotientData (directSumExtensionObject R S x)).obj ≅
      ((exactStructure R).extensionQuotientData x).obj :=
  IsColimit.coconePointUniqueUpToIso
    (((exactStructure R).extensionQuotientData (directSumExtensionObject R S x)).isColimit _)
    (isCokernelCoprodId S.of x.fiber.unop.hom.hom
      ((exactStructure R).extensionQuotientData x).π
      ((exactStructure R).extensionQuotientData x).zero
      (((exactStructure R).extensionQuotientData x).isColimit _))

/-- The quotient isomorphism is characterized on the original middle object. -/
@[reassoc]
theorem directSumExtensionQuotientIso_π (S : IsoCategory R)
    (x : (exactStructure R).ExtensionTotal) :
    ((exactStructure R).extensionQuotientData (directSumExtensionObject R S x)).π ≫
      (directSumExtensionQuotientIso R S x).hom =
        coprod.desc (0 : S.of ⟶ _) ((exactStructure R).extensionQuotientData x).π :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (((exactStructure R).extensionQuotientData (directSumExtensionObject R S x)).isColimit _)
    _ WalkingParallelPair.one

end ModuleCat.FiniteProjective
