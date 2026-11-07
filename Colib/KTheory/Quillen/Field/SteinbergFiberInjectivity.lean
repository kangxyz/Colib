/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Quillen.Field.SteinbergFiberTransgression
public import Colib.Topology.HomotopyFiber.CommutingSquareCapping
import Mathlib.Tactic.FinCases

/-!
# Injectivity of the original Steinberg-kernel map to Quillen K-two

The actual compact-square construction supplies the ordered axes and whole target
homotopy. The proved geometric transgression and native negative central evaluation
send every original torus defect back to itself. Actual kernel generation then gives
a left inverse of the original right-projective Quillen map.

Adapted from `Quillen/KTheory/Field/SteinbergFiberInjectivity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native group homology and central
evaluation rather than the former Schur equivalence. No assumed detector law is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Topology HomotopyGroup
open scoped commutatorElement

namespace ModuleCat.FiniteProjective.StableCompletion
open FundamentalGroupoid.LocalCoefficients
open HomotopyFiber.PeriodicConnecting HomotopyFiber.CommutingSquareCapping
variable (F : Type u) [Field F] {T : Type (u + 1)} [TopologicalSpace T]
  (q : C(T, ZeroComponent F)) (e : T) (he : q e = stableZeroMap F (stableBase F))
  (hq : IsCoveringMap q) [SimplyConnectedSpace T]

/-- Constructed capping data calibrate the actual kernel detector on every original
ordered torus defect. No geometric existence or transgression law is a hypothesis. -/
theorem originalKTwoKernelDetector_torus (a b : Fˣ) :
    originalKTwoKernelDetector F q e he hq
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) =
        StableSteinberg.torusDefectKernel a b := by
  let z := stableZeroCoverPoint F q e he
  let k := Covering.Pullback.lift (stableZeroMap F) q
  let E := coverElementaryEquiv F q e he hq
  let g := E.symm (StableSteinberg.toElementary F (StableSteinberg.h a))
  let h := E.symm (StableSteinberg.toElementary F (StableSteinberg.h02 b))
  have helem : Commute (StableSteinberg.toElementary F (StableSteinberg.h a))
      (StableSteinberg.toElementary F (StableSteinberg.h02 b)) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement, StableSteinberg.commutator_h_h02]
    exact (StableSteinberg.torusDefectKernel a b).property
  have hgh : Commute g h := helem.map E.symm.toMonoidHom
  obtain ⟨A, B, hArep, hBrep, hAB⟩ := exists_commuting_loop_representatives g h hgh
  let σ := sourceSquare A B hAB
  let β := targetCube A B hAB k
  let H₀ := wholeHomotopy A B hAB k
  have hsquare : basedSquare β = cubeSquare e β := by
    ext w
    apply congrArg β
    funext i
    fin_cases i <;> rfl
  let H : (k.comp σ).Homotopy (cubeSquare e β) := {
    toContinuousMap := H₀.toContinuousMap
    map_zero_left := H₀.apply_zero
    map_one_left := fun w => (H₀.apply_one w).trans
      (congrArg (fun f : C(unitInterval × unitInterval, T) => f w) hsquare) }
  have hx : σ (0, 0) = z := sourceSquare_vertex A B hAB
  have hσ₁ : ∀ t, σ (0, t) = σ (1, t) := (sourceSquare_periodic A B hAB).1
  have hσ₂ : ∀ t, σ (t, 0) = σ (t, 1) := (sourceSquare_periodic A B hAB).2
  have hH₁ : ∀ s t, H (s, (0, t)) = H (s, (1, t)) :=
    (wholeHomotopy_periodic A B hAB k).1
  have hH₂ : ∀ s t, H (s, (t, 0)) = H (s, (t, 1)) :=
    (wholeHomotopy_periodic A B hAB k).2
  have hA : E (piMap 0 (ContinuousMap.id _) hx (SingularBar.firstAxisClass σ hσ₁)) =
      StableSteinberg.toElementary F (StableSteinberg.h a) := by
    exact (congrArg E (firstAxisClass_at_of_edge σ hσ₁ hx A
      (sourceSquare_zero_second A B hAB))).trans
        ((congrArg E hArep).trans (E.apply_symm_apply _))
  have hB : E (piMap 0 (ContinuousMap.id _) hx (SingularBar.secondAxisClass σ hσ₂)) =
      StableSteinberg.toElementary F (StableSteinberg.h02 b) := by
    exact (congrArg E (secondAxisClass_at_of_edge σ hσ₂ hx B
      (sourceSquare_zero_first A B hAB))).trans
        ((congrArg E hBrep).trans (E.apply_symm_apply _))
  exact originalKTwoKernelDetector_periodic F q e he hq a b σ β H hx
    hσ₁ hσ₂ hH₁ hH₂ hA hB

/-- The constructed detector is a left inverse to the original kernel-to-Quillen map. -/
theorem originalKTwoKernelDetector_left_inverse :
    (originalKTwoKernelDetector F q e he hq).comp (steinbergKernelToRightProjectiveKTwo F) =
      MonoidHom.id (StableSteinberg.toElementary F).ker := by
  apply kernelHom_ext_torusDefect F
  intro a b
  exact originalKTwoKernelDetector_torus F q e he hq a b

include q e he hq in
/-- Any actual simply connected cover gives injectivity of the original comparison. -/
theorem originalKTwoComparison_injective_with_cover :
    Function.Injective (steinbergKernelToRightProjectiveKTwo F) := by
  have hl : Function.LeftInverse (originalKTwoKernelDetector F q e he hq)
      (steinbergKernelToRightProjectiveKTwo F) := by
    intro a
    exact congrArg (fun k => k a) (originalKTwoKernelDetector_left_inverse F q e he hq)
  exact hl.injective

omit [SimplyConnectedSpace T] in
/-- The original Steinberg-kernel-to-right-projective K-two map is injective over every field.
The actual simply connected cover and every geometric calibration are constructed. -/
theorem steinbergKernelToRightProjectiveKTwo_injective :
    Function.Injective (steinbergKernelToRightProjectiveKTwo F) := by
  obtain ⟨T, t, q, hq, hqs, hT⟩ := exists_simplyConnected_zeroComponent_cover F
  let := t
  let := hT
  obtain ⟨e, he⟩ := hqs (stableZeroMap F (stableBase F))
  exact originalKTwoComparison_injective_with_cover F q e he hq

end ModuleCat.FiniteProjective.StableCompletion
