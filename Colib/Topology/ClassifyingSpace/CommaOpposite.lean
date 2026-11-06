/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module
public import Colib.Topology.ClassifyingSpace.Adjunction
public import Colib.Topology.ClassifyingSpace.Opposite

/-! Source: Quillen/CategoryTheory/TheoremB/StructuredComparison.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd, only the actual opposite comma equivalence.
Mathlib supplies the categorical equivalence; no Theorem B or fiber comparison is assumed. -/
@[expose] public noncomputable section
universe u
open CategoryTheory Opposite
namespace CategoryTheory
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The actual structured comma realization and the opposite-functor
costructured comma realization are homotopy equivalent. -/
def structuredCommaOppositeEquiv (d : D) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (StructuredArrow d F))
      (ClassifyingSpace (CostructuredArrow F.op (op d))) :=
  (TopCat.homeoOfIso (classifyingOppositeIso (StructuredArrow d F))).symm.toHomotopyEquiv.trans
    (equivalenceClassifyingHomotopyEquiv (structuredArrowOpEquivalence F d))

end CategoryTheory
