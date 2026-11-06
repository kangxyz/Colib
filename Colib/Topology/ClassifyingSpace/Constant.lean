/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Constant
public import Colib.Topology.ClassifyingSpace.Map

/-! # Constant maps and geometric realization -/
/-! Implementation provenance: adapted from
`Quillen/Topology/ClassifyingSpace/Constant.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual functors, maps and
basepoint tracks are retained, using native Colib lower owners. -/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory

/-- The nerve map of a constant functor is the constant simplicial map. -/
theorem nerveMap_const {C D : Type u} [Category.{v} C] [Category.{v} D] (d : D) :
    CategoryTheory.nerveMap ((Functor.const C).obj d) = SSet.const (nerveVertex d) := by
  rfl

/-- A constant functor induces a constant continuous map of classifying spaces. -/
@[simp]
theorem classifyingSpaceMap_const_direct {C D : Type u} [Category.{v} C] [Category.{v} D]
    (d : D) : classifyingSpaceMap ((Functor.const C).obj d) =
      TopCat.const (X := ClassifyingSpace C) (classifyingSpacePoint d) := by
  ext p
  exact SSet.realization_const_apply (nerveVertex d) p

end CategoryTheory
