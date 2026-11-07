/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Basic

/-!
# Homotopies of actual path-space fiber lifts

Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredIsoHomotopy.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual simplex families,
path coordinates, and endpoint data are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyFiber
/-- Endpoint-relative homotopies between nullhomotopies induce homotopies
between their actual path-space fiber lifts. -/
def fiberLiftNullhomotopyHomotopy {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(A, X)) (y : Y)
    (H K : (f.comp g).Homotopy (ContinuousMap.const A y))
    (R : H.toContinuousMap.HomotopyRel K.toContinuousMap
      (fun z : unitInterval × A ↦ z.1 = 0 ∨ z.1 = 1)) :
    (HomotopyFiber.lift f y g H).Homotopy (HomotopyFiber.lift f y g K) where
  toFun z := ⟨(g z.2, ⟨fun t ↦ R (z.1, (t, z.2)), by fun_prop⟩),
    (R.prop' z.1 (0, z.2) (Or.inl rfl)).trans (H.map_zero_left z.2),
    (R.prop' z.1 (1, z.2) (Or.inr rfl)).trans (H.map_one_left z.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (unitInterval × A) × unitInterval ↦ R (z.1.1, (z.2, z.1.2)))
      fun_prop
  map_zero_left x := by
    apply Subtype.ext
    apply _root_.Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact R.map_zero_left (t, x)
  map_one_left x := by
    apply Subtype.ext
    apply _root_.Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact R.map_one_left (t, x)

end Topology.HomotopyFiber
