/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Colib.Topology.Prespectrum.FiberConnectingStageZero
public import Colib.Topology.Prespectrum.StableLevelOne

/-!
# The signed level-one comparison for the stable fiber boundary

The original level-one stable equivalences each use one structure map. Consequently their fiber
boundary square retains the negative sign proved for that actual stabilization. Omega hypotheses
are required only for the two stated level-one equivalences.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberConnectingLevelOne.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual fiber coordinates, strict
structure maps, specified whole nullhomotopies, integer grading and connecting signs
are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u
namespace Topology.LoopPrespectrum

/-- The original level-one equivalences identify the two fiber boundaries with a minus sign. -/
theorem stableFiberConnecting_levelOneStableEquiv_sign {E F : LoopPrespectrum.{u}}
    (f : E ⟶ F) (hF : F.IsOmega) (hFib : (homotopyFiber f).IsOmega)
    (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (a : HomotopyGroup.Pi (n + 2) (F.space 1) (F.point 1)) :
    stableFiberConnecting f (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup F) κ)
          (levelOneStableEquiv F hF (n + 1) (Additive.ofMul a))) =
      -(levelOneStableEquiv (homotopyFiber f) hFib n
        (Additive.ofMul (HomotopyFiber.connectingHom (f.map 1) (F.point 1)
          (E.point 1) (f.map_point 1) n a))) := by
  rw [levelOneStableEquiv_apply, levelOneStableEquiv_apply]
  exact stableFiberConnecting_nonnegativeLevelOne f n κ a

end Topology.LoopPrespectrum
