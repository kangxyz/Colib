/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.FiberLiftNaturality

/-!
# Signed connecting maps of specified fiber lifts

The connecting map of an actual composable pair with its specified null is
the original signed fiber connecting map followed by the inverse of the
stable group map of that null's fiber lift. Three maps preserving the two
arrows and every original null time give its naturality square.

Only the lift maps in the displayed degree must be invertible. The definition
does not select a new null or transport a boundary from another sequence.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberLiftConnecting.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual fiber coordinates, strict
structure maps, specified whole nullhomotopies, integer grading and connecting signs
are retained. -/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace Topology.LoopPrespectrum

variable {S A O S' A' O' : LoopPrespectrum.{u}}

/-- The original signed fiber boundary expressed through the specified degree-wise fiber lift. -/
def stableFiberLiftConnecting (f : S ⟶ A) (r : A ⟶ O)
    (N : Homotopy (f ≫ r) (zeroHom S O)) (d : ℤ)
    [IsIso ((stableHomotopyFunctor d).map (homotopyFiberLift r f N))] :
    stableHomotopyGroup O (d + 1) ⟶ stableHomotopyGroup S d :=
  stableFiberConnecting r d ≫
    inv ((stableHomotopyFunctor d).map (homotopyFiberLift r f N))

/-- Following the connecting map by its original lift recovers the signed fiber boundary. -/
@[reassoc]
theorem stableFiberLiftConnecting_comp_lift (f : S ⟶ A) (r : A ⟶ O)
    (N : Homotopy (f ≫ r) (zeroHom S O)) (d : ℤ)
    [IsIso ((stableHomotopyFunctor d).map (homotopyFiberLift r f N))] :
    stableFiberLiftConnecting f r N d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift r f N) =
      stableFiberConnecting r d := by
  simp only [stableFiberLiftConnecting, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

/-- The equation with the original fiber lift uniquely determines this connecting map. -/
theorem stableFiberLiftConnecting_unique (f : S ⟶ A) (r : A ⟶ O)
    (N : Homotopy (f ≫ r) (zeroHom S O)) (d : ℤ)
    [IsIso ((stableHomotopyFunctor d).map (homotopyFiberLift r f N))]
    (δ : stableHomotopyGroup O (d + 1) ⟶ stableHomotopyGroup S d)
    (hδ : δ ≫ (stableHomotopyFunctor d).map (homotopyFiberLift r f N) =
      stableFiberConnecting r d) :
    δ = stableFiberLiftConnecting f r N d := by
  apply (cancel_mono ((stableHomotopyFunctor d).map (homotopyFiberLift r f N))).1
  exact hδ.trans (stableFiberLiftConnecting_comp_lift f r N d).symm

/-- Actual arrow squares and the same whole null preserve the signed connecting map. -/
theorem stableFiberLiftConnecting_naturality
    (f : S ⟶ A) (r : A ⟶ O) (f' : S' ⟶ A') (r' : A' ⟶ O')
    (N : Homotopy (f ≫ r) (zeroHom S O))
    (N' : Homotopy (f' ≫ r') (zeroHom S' O'))
    (s : S ⟶ S') (a : A ⟶ A') (o : O ⟶ O')
    (hf : f ≫ a = s ≫ f') (hr : a ≫ r' = r ≫ o)
    (hN : ∀ n t x, o.map n (N.level n (t, x)) = N'.level n (t, s.map n x))
    (d : ℤ)
    [IsIso ((stableHomotopyFunctor d).map (homotopyFiberLift r f N))]
    [IsIso ((stableHomotopyFunctor d).map (homotopyFiberLift r' f' N'))] :
    stableFiberLiftConnecting f r N d ≫ (stableHomotopyFunctor d).map s =
      (stableHomotopyFunctor (d + 1)).map o ≫
        stableFiberLiftConnecting f' r' N' d := by
  let sq : Arrow.mk r ⟶ Arrow.mk r' := Arrow.homMk a o hr
  have hL :
      (stableHomotopyFunctor d).map s ≫
          (stableHomotopyFunctor d).map (homotopyFiberLift r' f' N') =
        (stableHomotopyFunctor d).map (homotopyFiberLift r f N) ≫
          (stableHomotopyFunctor d).map (homotopyFiberMap sq) := by
    simpa only [Functor.map_comp] using congrArg (stableHomotopyFunctor d).map
      (homotopyFiberLift_naturality f r f' r' N N' s a o hf hr hN).symm
  apply (cancel_mono ((stableHomotopyFunctor d).map (homotopyFiberLift r' f' N'))).1
  calc
    (stableFiberLiftConnecting f r N d ≫ (stableHomotopyFunctor d).map s) ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift r' f' N') =
      stableFiberLiftConnecting f r N d ≫
        ((stableHomotopyFunctor d).map s ≫
          (stableHomotopyFunctor d).map (homotopyFiberLift r' f' N')) :=
      Category.assoc _ _ _
    _ = stableFiberConnecting r d ≫
        (stableHomotopyFunctor d).map (homotopyFiberMap sq) := by
      rw [hL, ← Category.assoc, stableFiberLiftConnecting_comp_lift]
    _ = (stableHomotopyFunctor (d + 1)).map o ≫ stableFiberConnecting r' d :=
      (stableFiberConnecting_naturality sq d).symm
    _ = ((stableHomotopyFunctor (d + 1)).map o ≫
        stableFiberLiftConnecting f' r' N' d) ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift r' f' N') := by
      rw [Category.assoc, stableFiberLiftConnecting_comp_lift]

end Topology.LoopPrespectrum
