/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.ClassifyingSpace.Path
public import Colib.Topology.Realization.Triangle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# The realized category-to-fundamental-groupoid functor

Extracted from `Quillen/Topology/ClassifyingSpace/ArrowPaths.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, endpoints,
relative homotopies, universe parameters and multiplication order are retained.
Only native namespace and import ownership change unless noted below.

This functor has the actual vertex objects and arrow path classes. Its
composition law uses the realized two-simplex, not edge-path approximation.
Fullness, faithfulness and essential surjectivity are not asserted.

-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Opposite
open scoped Simplicial Topology unitInterval
open SSet

namespace CategoryTheory

/-- The path of a composite categorical arrow agrees up to endpoint-fixed
homotopy with the concatenation of the two arrow paths. -/
theorem classifyingSpacePath_comp {C : Type u} [Category.{v} C]
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    ((classifyingSpacePath f).trans (classifyingSpacePath g)).Homotopic
      (classifyingSpacePath (f ≫ g)) :=
  realizationEdgePath_comp ((CategoryTheory.nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl).some

/-- Every category maps canonically into the actual fundamental groupoid of
its classifying space by realizing vertices and arrows. -/
def classifyingFundamentalGroupoidFunctor (C : Type u) [Category.{v} C] :
    C ⥤ FundamentalGroupoid (ClassifyingSpace C) where
  obj x := FundamentalGroupoid.mk (classifyingSpacePoint x)
  map f := ⟦classifyingSpacePath f⟧
  map_id x := by simp [classifyingSpacePath_id]; rfl
  map_comp f g := (Quotient.sound (classifyingSpacePath_comp f g)).symm

end CategoryTheory

attribute [colib_tag "COL-0085",
  colib_ref "WeibelKBook" "IV, Recipe 3.1.1 and Lemma 3.4, composition relation"
    "background"
    "Arrow-path composition via triangles, not the full fundamental-group presentation"]
  CategoryTheory.classifyingSpacePath_comp
  CategoryTheory.classifyingFundamentalGroupoidFunctor
