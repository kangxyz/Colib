/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.WeakComparison
public import Colib.CategoryTheory.TheoremB.StructuredWeakTransport

/-!
# Quillen's Theorem B in the structured-arrow convention

The actual contravariant structured-comma transition hypothesis implies
bijectivity of the canonical structured comparison on every based homotopy
set at the identity-arrow basepoint. The opposite-category realization and
its path-coordinate reversal preserve that specific comparison and basepoint.
No global homotopy inverse of the fiber comparison is asserted.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredWeakComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; actual comparisons and basepoints are retained. -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite Topology
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- Structured Theorem B at the actual identity-arrow basepoint, including
π₀, under only the actual structured transition hypothesis. -/
theorem structuredFiberComparison_bijective
    (h : StructuredTransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (structuredFiberComparison F (F.obj c)) (structuredFiberComparison_identity F c)) :=
  structuredFiberComparison_bijective_of_opposite F c n
    (fiberComparison_bijective F.op
      (transitionHomotopyEquivalences_op_of_structured F h) (op c) n)

/-- The structured comparison induces its canonical positive-degree group
isomorphism; no separately chosen unbased equivalence is substituted. -/
def structuredFiberComparisonPiEquiv
    (h : StructuredTransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (ClassifyingSpace (StructuredArrow (F.obj c) F))
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) ≃*
    HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c)))
      (HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c)) :=
  MulEquiv.ofBijective
    (HomotopyGroup.piMap n (structuredFiberComparison F (F.obj c))
      (structuredFiberComparison_identity F c))
    (structuredFiberComparison_bijective F h c (n + 1))

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem structuredFiberComparisonPiEquiv_coe
    (h : StructuredTransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    ↑(structuredFiberComparisonPiEquiv F h c n) =
      HomotopyGroup.piMap n (structuredFiberComparison F (F.obj c))
        (structuredFiberComparison_identity F c)
        := rfl

end CategoryTheory.TheoremB

attribute [colib_tag "COL-0248",
  colib_ref "WeibelKBook" "IV, 3.8, page 31" "adaptation"
    "The original transition homotopy-equivalence theorem, retaining actual comma-to-fiber maps"]
  CategoryTheory.TheoremB.structuredFiberComparison_bijective
  CategoryTheory.TheoremB.structuredFiberComparisonPiEquiv
  CategoryTheory.TheoremB.structuredFiberComparisonPiEquiv_coe
