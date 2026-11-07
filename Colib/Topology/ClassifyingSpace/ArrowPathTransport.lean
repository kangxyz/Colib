/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ArrowPaths
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportHomotopy

/-!
# Original basepoint transport along categorical inverse arrows

Realizing an inverse categorical arrow gives the reversed original edge up to
endpoint-fixed homotopy. Consequently its transport is inverse to the original
edge transport in every finite degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory Topology SSet HomotopyGroup

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {x y : C}

/-- The edge of the inverse is homotopic to the reversed edge, with endpoints fixed. -/
theorem classifyingSpacePath_inv_homotopic (e : x ≅ y) :
    (classifyingSpacePath e.inv).Homotopic (classifyingSpacePath e.hom).symm := by
  apply Path.Homotopic.Quotient.exact
  change (classifyingFundamentalGroupoidFunctor C).map e.inv =
    Groupoid.inv ((classifyingFundamentalGroupoidFunctor C).map e.hom)
  rw [Groupoid.inv_eq_inv, ← Functor.map_inv]
  exact congrArg _ (IsIso.eq_inv_of_hom_inv_id e.hom_inv_id)

/-- The original transports along an isomorphism and its inverse cancel in every degree. -/
@[simp]
theorem pathTransport_classifyingSpacePath_inv_hom (e : x ≅ y) (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace C) (classifyingSpacePoint x)) :
    pathTransport (classifyingSpacePath e.inv) n
      (pathTransport (classifyingSpacePath e.hom) n a) = a := by
  rw [pathTransport_eq_of_homotopic (classifyingSpacePath_inv_homotopic e)]
  exact pathTransport_symm_apply _ _ _

end CategoryTheory
