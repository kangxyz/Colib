/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.StableZeroFiberGeometry
public import Colib.Topology.HomotopyFiber.H2Perfectness

/-!
# Perfectness of the original stable completion fiber group

For every ring, the constructed simply connected cover and its actual pullback
supply the geometric and integral homology hypotheses of the proved low-degree
criterion. The original endpoint-aware fiber map transfers perfectness to the
literal stable-zero homotopy fiber at its canonical constant-path point.
For fields, this is definitionally the fiber already used by the Steinberg comparison.
-/

/-! Implementation source: `Quillen/KTheory/Plus/StableFiberPerfectness.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The map, cover pullback,
basepoint and endpoint-aware fiber comparison are the actual original ones. -/
@[expose] public section
noncomputable section
universe u
open Topology
namespace ModuleCat.FiniteProjective.StableCompletion

/-- The original stable-zero homotopy fiber has perfect Pi one for every ring. -/
theorem stableZeroFiber_piOne_isPerfect (R : Type u) [Ring R] :
    Group.IsPerfect (HomotopyGroup.Pi 1
      (HomotopyFiber (stableZeroMap R) (stableZeroMap R (stableBase R)))
      (HomotopyFiber.basepoint (stableZeroMap R) (stableZeroMap R (stableBase R))
        (stableBase R) rfl)) := by
  obtain ⟨T, t, setup⟩ := exists_stableZeroCover_homologicalSetup R
  let := t
  obtain ⟨q, e, he, _hq, _hqs, hT, hP, hp, hH, hm⟩ := setup
  let := hT
  let := hP
  let := hp
  let : Group.IsPerfect
      (HomotopyGroup.Pi 1 (HomotopyFiber (Covering.Pullback.lift (stableZeroMap R) q) e)
        (HomotopyFiber.basepoint (Covering.Pullback.lift (stableZeroMap R) q) e
          (stableZeroCoverPoint R q e he) rfl)) :=
    HomotopyFiber.piOne_isPerfect_of_singular_quasiIso
      (Covering.Pullback.lift (stableZeroMap R) q) e (stableZeroCoverPoint R q e he) rfl hH
  exact Group.IsPerfect.ofSurjective hm.surjective

end ModuleCat.FiniteProjective.StableCompletion
