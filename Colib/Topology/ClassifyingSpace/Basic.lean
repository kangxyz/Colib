/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Based classifying spaces and shifted homotopy groups

For a category `C`, its classifying space is the genuine geometric realization
of its nerve. An object `c : C` supplies a vertex and hence a point of this
space. We define the shifted homotopy groups `π_(n+1) (|nerve C|) c` using
mathlib's quotient of based continuous maps by based homotopy.

This file is generic infrastructure. It does not assert that an arbitrary
category defines Quillen K-theory. The Quillen construction must first supply
the appropriate Q-category and its distinguished object.

The shifted group in degree zero is only a group in this generality. The
positive-degree shifted groups are commutative, by the existing
Eckmann–Hilton theorem for higher homotopy groups.

## Implementation provenance

Adapted from `Quillen/Topology/ClassifyingSpace/Basic.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Only namespace ownership changes:
the realized nerve, vertex, based homotopy quotient, universes, and degree shift
are retained. Mathlib supplies all three underlying constructions.
-/
@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- The classifying space of a category, using mathlib's geometric realization
functor. This is a topological space, not a formal placeholder for one. -/
def ClassifyingSpace : TopCat.{max u v} :=
  SSet.toTop.obj (CategoryTheory.nerve C)

variable {C}

/-- The zero-simplex of the nerve determined by an object. -/
def nerveVertex (c : C) : (CategoryTheory.nerve C).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀ c

/-- The map from the standard zero-simplex selecting the vertex `c`. -/
def nerveVertexMap (c : C) : (Δ[0] : SSet.{max u v}) ⟶ CategoryTheory.nerve C :=
  SSet.yonedaEquiv.symm (nerveVertex c)

/-- The point of the classifying space represented by the object `c`.
It is the image of the unique point of the realized zero-simplex. -/
def classifyingSpacePoint (c : C) : ClassifyingSpace C :=
  SSet.toTop.map (nerveVertexMap c) default

section Functoriality

variable {D : Type u} [Category.{v} D] (F : C ⥤ D)

/-- The continuous map of classifying spaces induced by a functor. -/
def classifyingSpaceMap : ClassifyingSpace C ⟶ ClassifyingSpace D :=
  SSet.toTop.map (CategoryTheory.nerveMap F)

/-- A functor sends the vertex for an object to the vertex for its image. -/
@[simp]
theorem nerveVertexMap_comp (c : C) :
    nerveVertexMap c ≫ CategoryTheory.nerveMap F = nerveVertexMap (F.obj c) := by
  exact (SSet.yonedaEquiv_symm_comp (X := CategoryTheory.nerve C)
    (n := ⦋0⦌) (nerveVertex c) (CategoryTheory.nerveMap F)).trans
      (congrArg SSet.yonedaEquiv.symm (CategoryTheory.nerveMap_app_mk₀ F c))

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality preserves the chosen point when the chosen object is mapped
by the functor. -/
@[simp]
theorem classifyingSpaceMap_point (c : C) :
    classifyingSpaceMap F (classifyingSpacePoint c) =
      classifyingSpacePoint (F.obj c) := by
  have h := congrArg
    (fun f : (Δ[0] : SSet.{max u v}) ⟶ CategoryTheory.nerve D ↦
      SSet.toTop.map f default)
    (nerveVertexMap_comp F c)
  simpa only [Functor.map_comp, TopCat.comp_app, classifyingSpaceMap,
    classifyingSpacePoint, ClassifyingSpace] using h

end Functoriality

/-- The shifted homotopy group of a based classifying space.

This is the actual `(n + 1)`st homotopy group. Quillen K-groups arise only after
instantiating this construction with the appropriate Q-category. -/
def ShiftedHomotopyGroup (C : Type u) [Category.{v} C] (c : C) (n : ℕ) :=
  HomotopyGroup.Pi (n + 1) (ClassifyingSpace C) (classifyingSpacePoint c)

/-- Every shifted homotopy group has mathlib's homotopy-group structure. -/
instance shiftedHomotopyGroupGroup (c : C) (n : ℕ) :
    Group (ShiftedHomotopyGroup C c n) :=
  inferInstanceAs
    (Group (HomotopyGroup.Pi (n + 1) (ClassifyingSpace C) (classifyingSpacePoint c)))

/-- In positive shifted degree the homotopy group is commutative.
The underlying group operation is inherited from mathlib's higher homotopy
group instance, whose commutativity is proved by Eckmann–Hilton. -/
instance shiftedHomotopyGroupCommGroup (c : C) (n : ℕ) :
    CommGroup (ShiftedHomotopyGroup C c (n + 1)) :=
  inferInstanceAs
    (CommGroup (HomotopyGroup.Pi ((n + 1) + 1)
      (ClassifyingSpace C) (classifyingSpacePoint c)))

/-- The same commutative-group structure with an explicit positive-degree
hypothesis, useful when the index is not syntactically a successor. -/
abbrev shiftedHomotopyGroupCommGroupOfPositive (c : C) (n : ℕ) (hn : 1 ≤ n) :
    CommGroup (ShiftedHomotopyGroup C c n) := by
  letI : Nontrivial (Fin (n + 1)) :=
    Fin.nontrivial_iff_two_le.mpr (Nat.succ_le_succ hn)
  exact inferInstanceAs
    (CommGroup (HomotopyGroup.Pi (n + 1)
      (ClassifyingSpace C) (classifyingSpacePoint c)))

end CategoryTheory

attribute [colib_tag "COL-0043",
  colib_ref "WeibelKBook"
    "IV, Definition 3.1.4 and the following realization definition" "adaptation"
    "The realized nerve and its actual point selected by an object vertex"]
  CategoryTheory.ClassifyingSpace
  CategoryTheory.classifyingSpacePoint
