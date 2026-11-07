/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionComma
public import Colib.Topology.ClassifyingSpace.ProjectiveZeroFiber

/-! # Realization of the actual zero-fiber/comma comparison -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Topology SSet HomotopyGroup
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- The genuine fiber inclusion is a classifying-space homotopy equivalence. -/
def localizedExtensionFiberCommaClassifyingHomotopyEquiv
    (b : CategoryTheory.QConstruction (exactStructure R).deflation (exactStructure R).inflation) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (IsoFiber (localizedExtensionProjection R) b))
      (ClassifyingSpace (StructuredArrow b (localizedExtensionProjection R))) :=
  adjunctionClassifyingHomotopyEquivUniversal (localizedExtensionFiberCommaAdjunction R b)

@[simp]
theorem localizedExtensionFiberCommaClassifyingHomotopyEquiv_toFun
    (b : CategoryTheory.QConstruction (exactStructure R).deflation (exactStructure R).inflation) :
    (localizedExtensionFiberCommaClassifyingHomotopyEquiv R b).toFun =
      classifyingSpaceMapUniversal (IsoFiber.toStructured (localizedExtensionProjection R) b) :=
  adjunctionClassifyingHomotopyEquivUniversal_toFun _

/-- The original group-completion space identifies with the actual zero comma
space. Theorem B's transition hypothesis is still a separate obligation. -/
def completionZeroCommaClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (GroupCompletionCategory R))
      (ClassifyingSpace
        (StructuredArrow (exactStructure R).qZero (localizedExtensionProjection R))) :=
  (completionZeroIsoFiberClassifyingHomotopyEquiv R).trans
    (localizedExtensionFiberCommaClassifyingHomotopyEquiv R (exactStructure R).qZero)

end ModuleCat.FiniteProjective
