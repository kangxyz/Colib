/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.SimplicialMap
public import Colib.KTheory.Waldhausen.Basic
public import Colib.KTheory.Quillen.Basic
public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-! # The chosen zero point of the canonical Q/S comparison

Both arrows of the canonical comparison zigzag preserve the actual chosen
zero vertex. This gives genuine homomorphisms on shifted homotopy groups,
without asserting that the Q/S comparison is a weak equivalence.

Adapted from `Quillen/Waldhausen/QuillenComparison/Basepoint.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, on the canonical native simplicial map.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject
universe v u

namespace CategoryTheory.Waldhausen.QuillenComparison
open SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- The zero vertex of the edgewise S-construction. -/
def subdivisionZeroVertex :
    (EdgewiseSubdivision.subdivision
      (sSet E.inflation (MorphismProperty.isomorphisms C))).obj (op ⦋0⦌) :=
  zeroSimplex E.inflation (MorphismProperty.isomorphisms C) (0 : C) (isZero_zero C) _

/-- The Q/S map takes the zero diagram to the original Q zero vertex. -/
@[simp]
theorem comparisonMap_zeroVertex :
    (comparisonMap E).app (op ⦋0⦌) (subdivisionZeroVertex E) =
      nerveVertex (QConstruction.of E.deflation E.inflation (0 : C)) := by
  apply ComposableArrows.ext₀
  rfl

/-- The edgewise endpoint map also preserves the chosen zero vertex. -/
@[simp]
theorem endpoint_zeroVertex :
    (EdgewiseSubdivision.endpoint (sSet E.inflation (MorphismProperty.isomorphisms C))).app (op ⦋0⦌)
      (subdivisionZeroVertex E) =
      zeroSimplex E.inflation (MorphismProperty.isomorphisms C) (0 : C) (isZero_zero C) (op ⦋0⦌)
        := rfl

/-- The actual realization on the common source of the comparison zigzag. -/
def SubdivisionSpace : TopCat.{max u v} :=
  SSet.toTop.obj
    (EdgewiseSubdivision.subdivision (sSet E.inflation (MorphismProperty.isomorphisms C)))

/-- Its point is the realization of the all-zero subdivided simplex. -/
def subdivisionBasepoint : SubdivisionSpace E :=
  SSet.toTop.map (SSet.yonedaEquiv.symm (subdivisionZeroVertex E)) default

/-- The canonical continuous map from the subdivided S-model to Q. -/
def realizationComparison : SubdivisionSpace E ⟶ E.KSpace :=
  SSet.toTop.map (comparisonMap E)

/-- The canonical endpoint map to the existing exact-category S-model. -/
def realizationEndpoint : SubdivisionSpace E ⟶ (ofExactCategory E).Delooping :=
  SSet.toTop.map (EdgewiseSubdivision.endpoint (sSet E.inflation (MorphismProperty.isomorphisms C)))

@[simp]
theorem realizationComparison_basepoint :
    realizationComparison E (subdivisionBasepoint E) = E.kBasepoint := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (subdivisionZeroVertex E)) ≫
    SSet.toTop.map (comparisonMap E)) default = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp, comparisonMap_zeroVertex]
  rfl

@[simp]
theorem realizationEndpoint_basepoint :
    realizationEndpoint E (subdivisionBasepoint E) = (ofExactCategory E).kBasepoint := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (subdivisionZeroVertex E)) ≫
    SSet.toTop.map
      (EdgewiseSubdivision.endpoint (sSet E.inflation (MorphismProperty.isomorphisms C))))
      default = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp, endpoint_zeroVertex]
  rfl

/-- Actual shifted homotopy groups of the common subdivided source. -/
abbrev SubdivisionK (n : ℕ) :=
  HomotopyGroup.Pi (n + 1) (SubdivisionSpace E) (subdivisionBasepoint E)

/-- The based Q/S comparison homomorphism on the subdivided source. -/
def subdivisionComparisonK (n : ℕ) : SubdivisionK E n →* E.K n :=
  HomotopyGroup.piMap n (realizationComparison E).hom (realizationComparison_basepoint E)

/-- The other based homomorphism in the actual comparison zigzag. -/
def subdivisionEndpointK (n : ℕ) : SubdivisionK E n →* (ofExactCategory E).K n :=
  HomotopyGroup.piMap n (realizationEndpoint E).hom (realizationEndpoint_basepoint E)

end CategoryTheory.Waldhausen.QuillenComparison

attribute [colib_tag "COL-0243",
  colib_ref "quillen" "Quillen/Waldhausen/QuillenComparison/Basepoint.lean"
    "adaptation" "The actual zero-based Q/S comparison zigzag and its shifted group maps"]
  CategoryTheory.Waldhausen.QuillenComparison.comparisonMap_zeroVertex
  CategoryTheory.Waldhausen.QuillenComparison.realizationComparison
  CategoryTheory.Waldhausen.QuillenComparison.realizationComparison_basepoint
  CategoryTheory.Waldhausen.QuillenComparison.realizationEndpoint_basepoint
  CategoryTheory.Waldhausen.QuillenComparison.subdivisionComparisonK
  CategoryTheory.Waldhausen.QuillenComparison.subdivisionEndpointK
