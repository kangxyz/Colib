/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-! # Detecting actual path connectedness on the zeroth homotopy set

Implementation provenance:
`Quillen/Topology/HomotopyGroups/ZeroDetection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
universe u v

namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Path connectedness gives a subsingleton for the original finite-zero
homotopy set at any displayed point. -/
theorem subsingleton_homotopyGroup_zero [PathConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup (Fin 0) X x) :=
  (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).injective.subsingleton

/-- Injectivity of the actual zeroth homotopy map into a connected space
forces the source, at the supplied point, to be genuinely path connected. -/
theorem pathConnectedSpace_of_injective_zeroMap [PathConnectedSpace Y]
    (f : C(X, Y)) (x : X)
    (h : Function.Injective (HomotopyGroup.map (N := Fin 0) f (x := x) rfl)) :
    PathConnectedSpace X := by
  let := subsingleton_homotopyGroup_zero (f x)
  let : Subsingleton (HomotopyGroup (Fin 0) X x) := h.subsingleton
  let : Subsingleton (ZerothHomotopy X) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm.injective.subsingleton
  exact pathConnectedSpace_iff_zerothHomotopy.2 ⟨⟨ZerothHomotopy.mk x⟩, inferInstance⟩

/-- Every actual map between path-connected spaces is bijective on the
zeroth homotopy sets; this does not identify π₀ with a group. -/
theorem homotopyGroupMap_zero_bijective [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (x : X) :
    Function.Bijective (HomotopyGroup.map (N := Fin 0) f (x := x) rfl) := by
  let := subsingleton_homotopyGroup_zero x
  let := subsingleton_homotopyGroup_zero (f x)
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
    fun _ ↦ ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ _⟩⟩

end Topology
