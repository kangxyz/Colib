/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionCartesian
public import Colib.CategoryTheory.FiberedCategory.IsoFiber.Cartesian

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveExtensionComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Actual isomorphism fibers and the original Q comma categories -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
variable (b : QConstruction (exactStructure R).deflation (exactStructure R).inflation)

/-- The actual fiber-to-comma inclusion has a right adjoint, by the cartesian
lifts proved for the original localized projection. -/
instance localizedExtensionFiberInclusion_isLeftAdjoint :
    (IsoFiber.toStructured (localizedExtensionProjection R) b).IsLeftAdjoint :=
  IsoFiber.toStructured_isLeftAdjoint_of_lifts _ _ fun U =>
    exists_localizedExtensionLift R U.right b U.hom

/-- Pull a comma object back to the original isomorphism fiber. -/
def localizedExtensionCommaRetraction :
    StructuredArrow b (localizedExtensionProjection R) ⥤
      IsoFiber (localizedExtensionProjection R) b :=
  Functor.rightAdjoint (IsoFiber.toStructured (localizedExtensionProjection R) b)

/-- The actual adjunction supplies both homotopies in the fiber/comma comparison. -/
def localizedExtensionFiberCommaAdjunction :
    IsoFiber.toStructured (localizedExtensionProjection R) b ⊣
      localizedExtensionCommaRetraction R b :=
  Adjunction.ofIsLeftAdjoint _

end ModuleCat.FiniteProjective
