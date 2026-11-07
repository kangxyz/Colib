/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.Basic

/-!
# Original paths for the homotopy pullback of two subspace inclusions

The existing strict-square comparison sends an actual overlap point to its constant path.
The stored path determines both actual endpoint coordinates, so its equality detects equality
in this homotopy pullback. Continuous path families with their original endpoint membership
proofs give the corresponding actual homotopy-pullback maps.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/OverlapPaths.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u v

namespace Topology.HomotopyPullback

variable {X : Type v} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (U V : Set Y)

/-- The original constant-path comparison of the two literal subspace inclusions. -/
def overlapComparison :
    C(↥(U ∩ V), HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)) :=
  comparison (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)
    ⟨fun x ↦ ⟨x.val, x.property.2⟩, by fun_prop⟩
    ⟨fun x ↦ ⟨x.val, x.property.1⟩, by fun_prop⟩ rfl

/-- The original overlap comparison is injective on its actual source points. -/
theorem overlapComparison_injective : Function.Injective (overlapComparison U V) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z ↦ z.val.1.val) h)

variable {U V}

/-- The original interval family, with the path coordinate placed before its parameter. -/
def overlapColumnFamily
    (b : C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V))) :
    C(unitInterval × X, Y) := ⟨fun z ↦ (b z.2).val.2.2 z.1, by fun_prop⟩

/-- In the subspace pullback the original stored path determines both endpoint coordinates. -/
theorem overlap_path_ext
    {z w : HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)}
    (h : z.val.2.2 = w.val.2.2) : z = w := by
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (z.property.2.symm.trans
      ((ContinuousMap.congr_fun h 1).trans w.property.2))
  · exact Prod.ext (Subtype.ext (z.property.1.symm.trans
      ((ContinuousMap.congr_fun h 0).trans w.property.1))) h

/-- An actual family of paths with endpoints in the two charts defines the original
homotopy-pullback family, with exactly those paths and endpoint values. -/
def ofOverlapColumns (b : C(unitInterval × X, Y))
    (hleft : ∀ x, b (0, x) ∈ U) (hright : ∀ x, b (1, x) ∈ V) :
    C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)) where
  toFun x := ⟨(⟨b (1, x), hright x⟩, ⟨b (0, x), hleft x⟩,
    ⟨fun t ↦ b (t, x), by fun_prop⟩), rfl, rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact b.continuous.comp continuous_swap

end Topology.HomotopyPullback
