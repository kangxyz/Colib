/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.StructuredComparison

/-! # The structured identity comparison at an equal target object

Adapted from `Quillen/Localization/Serre/StructuredComparisonWeak.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This is a generic exact basepoint identity, not a
weak-equivalence assertion or a hypothesis-transport adapter.
-/

@[expose] public noncomputable section

open CategoryTheory Topology
universe u
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- At an identity structured arrow transported along object equality, the
comparison is exactly the displayed constant-path basepoint. -/
theorem structuredFiberComparison_identity_of_eq (c : C) (d : D) (h : F.obj c = d) :
    structuredFiberComparison F d
      (classifyingSpacePoint (StructuredArrow.mk (eqToHom h.symm))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint d)
        (classifyingSpacePoint c)
        ((classifyingSpaceMap_point F c).trans (congrArg classifyingSpacePoint h)) := by
  subst d
  exact structuredFiberComparison_identity F c

end CategoryTheory.TheoremB
