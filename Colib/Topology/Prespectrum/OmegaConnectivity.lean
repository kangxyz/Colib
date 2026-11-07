/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StableOmega
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Vanishing

/-!
# Actual finite connectivity of connected Omega-prespectrum levels

The original structure equivalences prove increasing homotopy-set vanishing. Actual paths
transfer this to every point, including degree zero. An original map between these levels is
`n`-connected at level `n+1`, and the original level-to-point map is `n+1`-connected. Both bounds
use the actual path-space fiber convention and include target-component coverage.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/OmegaConnectivity.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual cone, full independent cylinder and loop parameters, signed degrees and
original hypotheses are retained under their native mathematical owners. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Original Omega shifts and paths give the finite vanishing bound at every positive-level point.
-/
theorem positiveLevel_homotopyGroup_subsingleton_at
    (E : LoopPrespectrum.{u}) (hE : E.IsOmega)
    (hconn : ∀ n, PathConnectedSpace (E.space (n + 1)))
    (n k : ℕ) (hk : k ≤ n) (x : E.space (n + 1)) :
    Subsingleton (HomotopyGroup.Pi k (E.space (n + 1)) x) := by
  let := hconn n
  let := homotopyGroup_subsingleton_of_lt E hE hconn k (n + 1) (by omega)
  let e := pathTransport (PathConnectedSpace.joined x (E.point (n + 1))).somePath k
  exact e.injective.subsingleton

/-- The literal original level-to-point map has the sharper full level connectivity bound. -/
theorem positiveLevel_toPoint_isHomotopyConnectedMap
    (E : LoopPrespectrum.{u}) (hE : E.IsOmega)
    (hconn : ∀ n, PathConnectedSpace (E.space (n + 1))) (n : ℕ) :
    IsHomotopyConnectedMap
      (ContinuousMap.const (E.space (n + 1)) (PUnit.unit : PUnit.{u + 1})) (n + 1) :=
  isHomotopyConnectedMap_const_of_vanishing (E.point (n + 1)) (n + 1)
    (fun x k hk ↦ positiveLevel_homotopyGroup_subsingleton_at E hE hconn n k (by omega) x)

/-- Any unchanged original map has increasing finite connectivity between connected Omega levels.
-/
theorem positiveLevel_isHomotopyConnectedMap
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (hE : E.IsOmega) (hF : F.IsOmega)
    (hcE : ∀ n, PathConnectedSpace (E.space (n + 1)))
    (hcF : ∀ n, PathConnectedSpace (F.space (n + 1))) (n : ℕ) :
    IsHomotopyConnectedMap (f.map (n + 1)) n := by
  let := hcF n
  exact isHomotopyConnectedMap_of_vanishing (f.map (n + 1)) (E.point (n + 1)) n
    (fun x k hk ↦ positiveLevel_homotopyGroup_subsingleton_at E hE hcE n k (by omega) x)
    (fun y k hk ↦ positiveLevel_homotopyGroup_subsingleton_at F hF hcF n k hk y)

end Topology.LoopPrespectrum
