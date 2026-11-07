/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StableEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Basic
public import Colib.CategoryTheory.Limits.Shapes.SequentialSystem.EventuallyIso

/-!
# Stabilization of growing finite bounds on the original prespectrum map

The original signed stable systems see only a tail of levels. A linear finite
range of slope two therefore makes their actual component maps eventually invertible. This
proves stable equivalence of the unchanged arrow, without replacing either prespectrum or any
stable transition. The explicit signed indexing also includes every negative degree.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StableConnectivity.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual cone, full independent cylinder and loop parameters, signed degrees and
original hypotheses are retained under their native mathematical owners. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum

/-- Eventual slope-two finite range makes the unchanged map stable in every signed degree. -/
theorem isStableEquivalence_of_eventually_linearConnectivity {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (N c : ℕ) (hf : ∀ n, N ≤ n →
      IsHomotopyConnectedMap (f.map (n + 1)) (2 * n - c)) :
    IsStableEquivalence f := by
  intro d
  change IsIso (colimMap (stableSystemMap f d))
  apply CategoryTheory.Limits.SequentialSystem.isIso_colimMap_of_eventually
    (stableSystemMap f d) (N + d.toNat + c + 1)
  intro n hn
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hb {y : F.space ((-d).toNat + n + 2)}
      (h : f.map ((-d).toNat + n + 2) (E.point ((-d).toNat + n + 2)) = y) :
      Function.Bijective (HomotopyGroup.map (N := Fin (d.toNat + n + 2))
        (f.map ((-d).toNat + n + 2)) h) := by
    cases h
    exact (hf ((-d).toNat + n + 1) (by omega)).homotopyGroupMap_bijective
      (E.point ((-d).toNat + n + 2)) (d.toNat + n + 2) (by omega)
  exact hb (f.map_point ((-d).toNat + n + 2))

/-- An original map with a slope-two finite range is a stable equivalence in every signed degree. -/
theorem isStableEquivalence_of_linearConnectivity {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (c : ℕ) (hf : ∀ n, IsHomotopyConnectedMap (f.map (n + 1)) (2 * n - c)) :
    IsStableEquivalence f :=
  isStableEquivalence_of_eventually_linearConnectivity f 0 c (fun n _ ↦ hf n)

end Topology.LoopPrespectrum
