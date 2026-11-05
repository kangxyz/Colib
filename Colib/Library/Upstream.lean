/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.LocalRing.Length
public import StacksCore.CategoryTheory.GrothendieckGroup.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeTwo

/-!
# Library membership for canonical upstream declarations

These registrations extend the index of mathematical results while retaining the original
Mathlib and Stacks objects, declaration names and proof implementations.
-/

attribute [colib_tag "COL-0001",
  colib_ref "WeibelKBook" "II, Definition 6.1.1" "generalization"
    "The source abelian-category case; Lean permits any category with zero morphisms"]
  CategoryTheory.GrothendieckGroup

attribute [colib_tag "COL-0002",
  colib_ref "WeibelKBook" "II, Definition 6.1.1, defining relation" "clause"
    "Additivity on a short exact sequence"] CategoryTheory.GrothendieckGroup.additivity

attribute [colib_tag "COL-0003",
  colib_ref "WeibelKBook" "II, paragraph 6.1.5" "generalization"
    "The source exact functor between abelian categories supplies the required hypothesis"]
  CategoryTheory.GrothendieckGroup.map

attribute [colib_tag "COL-0005",
  colib_ref "WeibelKBook" "III, Definition 7.1" "clause"
    "The graded tensor-algebra quotient and its homogeneous groups",
  colib_ref "Milnor1970" "Section 1, pp. 318-319, definition of the graded ring"
    "clause" "The tensor-algebra Steinberg quotient for a field"] MilnorKRing MilnorKTheory

attribute [colib_tag "COL-0006",
  colib_ref "WeibelKBook" "III, Definition 7.1, homogeneous components" "ingredient"
    "The induced internal grading on the Steinberg quotient"] milnorKGrading_isInternal

attribute [colib_tag "COL-0007",
  colib_ref "WeibelKBook" "III, Definition 7.1, degree two" "clause"
    "The tensor-square quotient by the degree-two Steinberg relations",
  colib_ref "Milnor1970" "Section 1, p. 319, tensor-quotient presentation"
    "clause" "The degree-two part of the presentation"]
  milnorKTwoEquivTensorProductQuotient

attribute [colib_tag "COL-0010"] IsLocalRing.length_restrictScalars
add_to_stacks 02M0 "single-local-ring length formula with extended lengths"
  IsLocalRing.length_restrictScalars
