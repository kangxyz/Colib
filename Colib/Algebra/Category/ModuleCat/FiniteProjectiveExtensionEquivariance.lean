/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionNaturality
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionFunctor

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionEquivariance.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Natural projection compatibility with actual direct-sum translations -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction

/-- The actual direct-sum action on the total extension category. -/
@[instance_reducible]
def extensionDirectSumAction :
    MonoidalLeftAction (IsoCategory R) (exactStructure R).ExtensionTotal := inferInstance

/-- The original Q projection is naturally unchanged by each actual direct-sum translation. -/
def directSumProjectionIso (S : IsoCategory R) :
    MonoidalLeftAction.actionLeft (exactStructure R).ExtensionTotal S ⋙
        (exactStructure R).extensionProjection ≅ (exactStructure R).extensionProjection :=
  NatIso.ofComponents
    (fun x => (exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R S x))
    (fun f => directSumProjection_naturality R (𝟙 S) f)

end ModuleCat.FiniteProjective
