/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.H2CapDescent
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Colib.GroupTheory.IsPerfect

/-!
# Perfectness of the original fiber group for an injective H-two surjection

The chain argument puts the original connecting image in the commutator.
The actual fiber exact sequence then has surjective projection to the perfect
source group, with kernel contained in the commutator. The elementary group
argument below proves perfectness of the original fiber group.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/InjectiveH2Perfectness.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the original actual fiber
projection, connecting homomorphism and genuine chain-cap descent. -/
@[expose] public section
noncomputable section
universe u v
open FundamentalGroupoid
namespace Topology.HomotopyFiber

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [PathConnectedSpace X] [SimplyConnectedSpace Y]

/-- The actual fiber of an injective integral H-two surjection has perfect Pi one
when the original source Pi one is perfect. -/
theorem piOne_isPerfect_of_injective_of_h2_surjective
    (j : C(X, Y)) (hj : Function.Injective j) (x : X)
    [Group.IsPerfect (HomotopyGroup.Pi 1 X x)]
    (hH : Function.Surjective (LocalCoefficients.pushforwardHomologyMap j
      (LocalCoefficients.constant Y LocalCoefficients.integralCoefficients.{u}) 2)) :
    Group.IsPerfect (HomotopyGroup.Pi 1 (HomotopyFiber j (j x))
      (basepoint j (j x) x rfl)) := by
  let p := HomotopyGroup.piMap 0 (projection j (j x)) (projection_basepoint j (j x) x rfl)
  have hp : Function.Surjective p := by
    apply MonoidHom.range_eq_top.mp
    change (HomotopyGroup.piMap 0 (projection j (j x))
      (projection_basepoint j (j x) x rfl)).range = ⊤
    rw [piMap_range_projection_eq_ker]
    let : Subsingleton (HomotopyGroup.Pi 1 Y (j x)) :=
      (HomotopyGroup.pi1EquivFundamentalGroup (X := Y) (x := j x)).injective.subsingleton
    ext a
    simp only [MonoidHom.mem_ker, Subgroup.mem_top, iff_true]
    exact Subsingleton.elim _ _
  have hk : p.ker ≤ commutator _ := by
    rw [show p = HomotopyGroup.piMap 0 (projection j (j x))
      (projection_basepoint j (j x) x rfl) from rfl,
      ← range_connectingHom_eq_ker_projection]
    exact LocalCoefficients.range_connectingHom_le_commutator_of_h2_surjective j hj x hH
  exact Group.IsPerfect.of_surjective_of_ker_le_commutator p hp hk

end Topology.HomotopyFiber
