/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Colib.Topology.Prespectrum.FiberConnectingStabilization

/-!
# The nonnegative stage-zero representative of the stable fiber boundary

The stable connecting map evaluates the original level-two connecting homomorphism with sign
plus one at stage zero. The equality-induced integer-degree transport remains explicit. No
Omega-spectrum hypothesis is needed: the theorem evaluates a specified representative.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberConnectingStageZero.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual fiber coordinates, strict
structure maps, specified whole nullhomotopies, integer grading and connecting signs
are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u
namespace Topology.LoopPrespectrum

/-- The original second-level class followed by the nonnegative stable stage-zero inclusion. -/
def nonnegativeStableHomotopyι (E : LoopPrespectrum.{u}) (n : ℕ) :
    Additive (HomotopyGroup.Pi (n + 2) (E.space 2) (E.point 2)) →+
      stableHomotopyGroup E (n : ℤ) :=
  (stableHomotopyι E (n : ℤ) 0).hom.comp (nonnegativeStableStageEquiv E n).toAddMonoidHom

/-- Nonnegative reindexing retains the original inverse loop shift at the second level. -/
theorem parameterStableStageIso_nonnegative (E : LoopPrespectrum.{u}) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 2) (Path (E.point 2) (E.point 2))
      (Path.refl (E.point 2))) :
    (shiftedStableReindexIso E (n : ℤ) 0).hom
        ((parameterStableStageIso E (n : ℤ) 0).hom
          (nonnegativeStableStageEquiv (parameterLooping E) n (Additive.ofMul a))) =
      nonnegativeStableStageEquiv E (n + 1)
        (Additive.ofMul ((loopShiftMulEquiv (x := E.point 2) (n + 1)).symm a)) := by
  cases n <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- At stage zero the stable inverse loop shift is the actual positive loop shift, with no minus. -/
theorem parameterStableHomotopyIso_inv_nonnegativeStageZero (E : LoopPrespectrum.{u})
    (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (a : HomotopyGroup.Pi (n + 3) (E.space 2) (E.point 2)) :
    (parameterStableHomotopyIso E (n : ℤ)).inv
        (eqToHom (congrArg (stableHomotopyGroup E) κ)
          (nonnegativeStableHomotopyι E (n + 1) (Additive.ofMul a))) =
      nonnegativeStableHomotopyι (parameterLooping E) n
        (Additive.ofMul (loopShiftMulEquiv (x := E.point 2) (n + 1) a)) := by
  have h := ConcreteCategory.congr_hom (parameterStableHomotopyIso_ι_inv E (n : ℤ) 0)
    (nonnegativeStableStageEquiv (parameterLooping E) n
      (Additive.ofMul (loopShiftMulEquiv (x := E.point 2) (n + 1) a)))
  change (parameterStableHomotopyIso E (n : ℤ)).inv
      (stableHomotopyι E ((n : ℤ) + 1) (parameterStableOffset (n : ℤ) + 0)
        ((shiftedStableReindexIso E (n : ℤ) 0).hom
          ((parameterStableStageIso E (n : ℤ) 0).hom
            (nonnegativeStableStageEquiv (parameterLooping E) n
              (Additive.ofMul (loopShiftMulEquiv (x := E.point 2) (n + 1) a)))))) =
    nonnegativeStableHomotopyι (parameterLooping E) n
      (Additive.ofMul (loopShiftMulEquiv (x := E.point 2) (n + 1) a)) at h
  rw [parameterStableStageIso_nonnegative, MulEquiv.symm_apply_apply] at h
  unfold parameterStableOffset at h
  split_ifs at h with hn
  · omega
  · simpa [hn, nonnegativeStableHomotopyι] using h

/-- The actual nonnegative stable inclusion is natural for the second-level homotopy map. -/
theorem nonnegativeStableHomotopyι_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (n : ℕ) (a : HomotopyGroup.Pi (n + 2) (E.space 2) (E.point 2)) :
    (stableHomotopyFunctor (n : ℤ)).map f
        (nonnegativeStableHomotopyι E n (Additive.ofMul a)) =
      nonnegativeStableHomotopyι F n
        (Additive.ofMul (HomotopyGroup.piMap (n + 1) (f.map 2) (f.map_point 2) a)) := by
  have h := ConcreteCategory.congr_hom (stableHomotopyι_naturality f (n : ℤ) 0)
    (nonnegativeStableStageEquiv E n (Additive.ofMul a))
  change _ = stableHomotopyι F (n : ℤ) 0
    ((stableSystemMap f (n : ℤ)).app 0
      (nonnegativeStableStageEquiv E n (Additive.ofMul a))) at h
  rw [← nonnegativeStableStageEquiv_naturality] at h
  exact h

/-- The stable fiber boundary on a nonnegative stage-zero representative has sign plus one. -/
theorem stableFiberConnecting_nonnegativeStageZero {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (a : HomotopyGroup.Pi (n + 3) (F.space 2) (F.point 2)) :
    stableFiberConnecting f (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup F) κ)
          (nonnegativeStableHomotopyι F (n + 1) (Additive.ofMul a))) =
      nonnegativeStableHomotopyι (homotopyFiber f) n
        (Additive.ofMul (HomotopyFiber.connectingHom (f.map 2) (F.point 2)
          (E.point 2) (f.map_point 2) (n + 1) a)) := by
  change (stableHomotopyFunctor (n : ℤ)).map (homotopyFiberLoopInclusion f)
    ((parameterStableHomotopyIso F (n : ℤ)).inv _) = _
  rw [parameterStableHomotopyIso_inv_nonnegativeStageZero F n κ]
  exact nonnegativeStableHomotopyι_naturality (homotopyFiberLoopInclusion f) n _

/-- A level-one representative acquires the explicit minus from its one stabilization step. -/
theorem stableFiberConnecting_nonnegativeLevelOne {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (a : HomotopyGroup.Pi (n + 2) (F.space 1) (F.point 1)) :
    stableFiberConnecting f (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup F) κ)
          (nonnegativeStableHomotopyι F (n + 1)
            (Additive.ofMul (structurePiMap F 1 (n + 1) a)))) =
      -(nonnegativeStableHomotopyι (homotopyFiber f) n
        (Additive.ofMul (structurePiMap (homotopyFiber f) 1 n
          (HomotopyFiber.connectingHom (f.map 1) (F.point 1)
            (E.point 1) (f.map_point 1) n a)))) := by
  rw [stableFiberConnecting_nonnegativeStageZero f n κ, connectingHom_structurePiMap_sign]
  exact map_neg (nonnegativeStableHomotopyι (homotopyFiber f) n) _

end Topology.LoopPrespectrum
