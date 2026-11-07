/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.Quillen.Field.SteinbergCoverComparison
public import Colib.Topology.LocalCoefficients.SingularBarCalibration
public import Colib.Topology.HomotopyFiber.PeriodicConnecting
public import Colib.Topology.LocalCoefficients.SecondHurewiczSquare
import Mathlib.Tactic.FinCases

/-!
# The original periodic-square transgression into stable-fiber homology

The original chains, signs, maps, basepoints and stated hypotheses are retained.
-/
/-! Implementation source: `Quillen/KTheory/Field/SteinbergFiberTransgression.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual connecting inverse
sign and original Quillen transports are retained. The final target is the
original Steinberg kernel via native negative central evaluation.
-/
@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory Topology HomotopyGroup
open scoped commutatorElement
namespace ModuleCat.FiniteProjective.StableCompletion
open HomotopyFiber.PeriodicConnecting FundamentalGroupoid.LocalCoefficients
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original equality correction on Pi one retains exactly the displayed path cast. -/
theorem piMap_id_loopClass {z x : X} (hx : z = x) (p : Path z z) :
    piMap 0 (ContinuousMap.id X) hx (loopClass p) = loopClass (p.cast hx.symm hx.symm) := rfl

/-- The singular-bar first axis class is exactly the original based path class. -/
theorem firstAxisClass_eq (σ : C(unitInterval × unitInterval, X))
    (hσ : ∀ t, σ (0, t) = σ (1, t)) :
    SingularBar.firstAxisClass σ hσ = loopClass (SingularBar.firstAxis σ hσ) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [loopClass_toFundamentalGroup]
  exact HomotopyGroup.pi1MulEquivFundamentalGroup.apply_symm_apply _

/-- The singular-bar second axis class is exactly the original based path class. -/
theorem secondAxisClass_eq (σ : C(unitInterval × unitInterval, X))
    (hσ : ∀ t, σ (t, 0) = σ (t, 1)) :
    SingularBar.secondAxisClass σ hσ = loopClass (SingularBar.secondAxis σ hσ) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [loopClass_toFundamentalGroup]
  exact HomotopyGroup.pi1MulEquivFundamentalGroup.apply_symm_apply _

variable (f : C(X, Y)) (y : Y) (σ : C(unitInterval × unitInterval, X))
  (β : GenLoop (Fin 2) Y y) (H : (f.comp σ).Homotopy (cubeSquare y β))
  (x : X) (hx : σ (0, 0) = x)

/-- Projection of the actual first fiber axis retains the named source vertex correction. -/
theorem firstAxisAt_projection
    (hσ : ∀ t, σ (0, t) = σ (1, t))
    (hH : ∀ s t, H (s, (0, t)) = H (s, (1, t))) :
    piMap 0 (HomotopyFiber.projection f y) rfl
      (loopClass (firstAxisAt f y σ β H x hx hσ hH)) =
        piMap 0 (ContinuousMap.id X) hx (SingularBar.firstAxisClass σ hσ) := by
  rw [loopClass_map, firstAxisClass_eq, piMap_id_loopClass]
  apply congrArg loopClass
  ext t
  rfl

/-- Projection of the actual second fiber axis retains the same named source vertex correction. -/
theorem secondAxisAt_projection
    (hσ : ∀ t, σ (t, 0) = σ (t, 1))
    (hH : ∀ s t, H (s, (t, 0)) = H (s, (t, 1))) :
    piMap 0 (HomotopyFiber.projection f y) rfl
      (loopClass (secondAxisAt f y σ β H x hx hσ hH)) =
        piMap 0 (ContinuousMap.id X) hx (SingularBar.secondAxisClass σ hσ) := by
  rw [loopClass_map, secondAxisClass_eq, piMap_id_loopClass]
  apply congrArg loopClass
  ext t
  rfl

/-- The actual canonical connecting map computes the periodic commutator after the complete
endpoint equivalence and original inverse Pi-two path transport. -/
theorem connectingHom_periodic_at
    (hσ₁ : ∀ t, σ (0, t) = σ (1, t)) (hσ₂ : ∀ t, σ (t, 0) = σ (t, 1))
    (hH₁ : ∀ s t, H (s, (0, t)) = H (s, (1, t)))
    (hH₂ : ∀ s t, H (s, (t, 0)) = H (s, (t, 1))) :
    HomotopyFiber.connectingHom f (f x) x rfl 0
      ((pathTransportMulEquiv (vertexTrackAt f y σ β H x hx) 1).symm (Quotient.mk' β)) =
        ⁅(endpointPiOneEquiv f x y (vertexTrackAt f y σ β H x hx)).symm
            (loopClass (firstAxisAt f y σ β H x hx hσ₁ hH₁)),
          (endpointPiOneEquiv f x y (vertexTrackAt f y σ β H x hx)).symm
            (loopClass (secondAxisAt f y σ β H x hx hσ₂ hH₂))⁆⁻¹ := by
  let c := vertexTrackAt f y σ β H x hx
  let Φ := endpointPiOneEquiv f x y c
  have h := (endpointPiOneEquiv_connecting_inverse f x y c (Quotient.mk' β)).trans
    (connecting_eq_commutator_inv_at f y σ β H x hx hσ₁ hσ₂ hH₁ hH₂)
  have hh := congrArg Φ.symm h
  simpa only [Φ, c, map_inv, map_commutatorElement, MulEquiv.symm_apply_apply] using hh

end ModuleCat.FiniteProjective.StableCompletion

namespace ModuleCat.FiniteProjective.StableCompletion
open FundamentalGroupoid.LocalCoefficients groupHomology
open HomotopyFiber.PeriodicConnecting
variable (F : Type u) [Field F] {T : Type (u + 1)} [TopologicalSpace T]
  (q : C(T, ZeroComponent F)) (e : T) (he : q e = stableZeroMap F (stableBase F))
  (hq : IsCoveringMap q) [SimplyConnectedSpace T]

/-- A supplied actual periodic square with the original ordered source axes computes the
original Steinberg-kernel Pi-two class, including its full vertex path and inverse sign. -/
theorem steinbergKernelToCoverPiTwo_periodic (a b : Fˣ)
    (σ : C(unitInterval × unitInterval, Covering.Pullback.Space (stableZeroMap F) q))
    (β : GenLoop (Fin 2) T e)
    (H : ((Covering.Pullback.lift (stableZeroMap F) q).comp σ).Homotopy (cubeSquare e β))
    (hx : σ (0, 0) = stableZeroCoverPoint F q e he)
    (hσ₁ : ∀ t, σ (0, t) = σ (1, t)) (hσ₂ : ∀ t, σ (t, 0) = σ (t, 1))
    (hH₁ : ∀ s t, H (s, (0, t)) = H (s, (1, t)))
    (hH₂ : ∀ s t, H (s, (t, 0)) = H (s, (t, 1)))
    (hA : coverElementaryEquiv F q e he hq
      (piMap 0 (ContinuousMap.id _) hx (SingularBar.firstAxisClass σ hσ₁)) =
        StableSteinberg.toElementary F (StableSteinberg.h a))
    (hB : coverElementaryEquiv F q e he hq
      (piMap 0 (ContinuousMap.id _) hx (SingularBar.secondAxisClass σ hσ₂)) =
        StableSteinberg.toElementary F (StableSteinberg.h02 b)) :
    steinbergKernelToCoverPiTwo F q e he hq (StableSteinberg.torusDefectKernel a b) =
      ((pathTransportMulEquiv
        (vertexTrackAt (Covering.Pullback.lift (stableZeroMap F) q) e σ β H
          (stableZeroCoverPoint F q e he) hx) 1).symm (Quotient.mk' β))⁻¹ := by
  let k := Covering.Pullback.lift (stableZeroMap F) q
  let z := stableZeroCoverPoint F q e he
  let c := vertexTrackAt k e σ β H z hx
  let Φ := endpointPiOneEquiv k z e c
  let A₁ := loopClass (firstAxisAt k e σ β H z hx hσ₁ hH₁)
  let B₁ := loopClass (secondAxisAt k e σ β H z hx hσ₂ hH₂)
  let A := Φ.symm A₁
  let B := Φ.symm B₁
  have hAp : coverFiberProjection F q e he A =
      piMap 0 (ContinuousMap.id _) hx (SingularBar.firstAxisClass σ hσ₁) := by
    have hh := endpointPiOneEquiv_projection k z e c A
    change piMap 0 (HomotopyFiber.projection k e) rfl (Φ (Φ.symm A₁)) =
      coverFiberProjection F q e he A at hh
    rw [MulEquiv.apply_symm_apply] at hh
    exact hh.symm.trans (firstAxisAt_projection k e σ β H z hx hσ₁ hH₁)
  have hBp : coverFiberProjection F q e he B =
      piMap 0 (ContinuousMap.id _) hx (SingularBar.secondAxisClass σ hσ₂) := by
    have hh := endpointPiOneEquiv_projection k z e c B
    change piMap 0 (HomotopyFiber.projection k e) rfl (Φ (Φ.symm B₁)) =
      coverFiberProjection F q e he B at hh
    rw [MulEquiv.apply_symm_apply] at hh
    exact hh.symm.trans (secondAxisAt_projection k e σ β H z hx hσ₂ hH₂)
  have hAc : coverElementaryEquiv F q e he hq (coverFiberProjection F q e he A) =
      StableSteinberg.toElementary F (StableSteinberg.h a) := by rw [hAp]; exact hA
  have hBc : coverElementaryEquiv F q e he hq (coverFiberProjection F q e he B) =
      StableSteinberg.toElementary F (StableSteinberg.h02 b) := by rw [hBp]; exact hB
  have hcomm := steinbergToCoverFiber_torusDefect F q e he hq a b A B hAc hBc
  have hδ : HomotopyFiber.connectingHom k e z rfl 0
      ((pathTransportMulEquiv c 1).symm (Quotient.mk' β)) = ⁅A, B⁆⁻¹ :=
    connectingHom_periodic_at k e σ β H z hx hσ₁ hσ₂ hH₁ hH₂
  apply coverConnecting_injective F q e he hq
  rw [connecting_steinbergKernelToCoverPiTwo, map_inv, hδ, inv_inv]
  exact hcomm

end ModuleCat.FiniteProjective.StableCompletion

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory Topology HomotopyGroup
open scoped commutatorElement
namespace ModuleCat.FiniteProjective.StableCompletion
open FundamentalGroupoid.LocalCoefficients HomotopyFiber.PeriodicConnecting groupHomology
variable {X : Type u} [TopologicalSpace X]

/-- The two suppliers use the same actual two-coordinate based square. -/
theorem cubeSquare_eq_hurewiczSquare {y : X} (β : GenLoop (Fin 2) X y) :
    cubeSquare y β = SecondHurewiczSquare.cubeSquare β := by
  ext z
  apply congrArg β
  funext i
  fin_cases i <;> rfl

/-- Naming an equal square vertex changes its actual bar homology formula only by the
original equality-corrected Pi-one maps. -/
theorem hTwoMap_squareTwoCycle_at [PathConnectedSpace X]
    (σ : C(unitInterval × unitInterval, X))
    (hσ₁ : ∀ t, σ (0, t) = σ (1, t)) (hσ₂ : ∀ t, σ (t, 0) = σ (t, 1))
    (p : X) (hp : σ (0, 0) = p) :
    SingularBar.hTwoMap p ((SecondHurewicz.Chains X).homologyπ 2
      (SingularBar.squareTwoCycle σ hσ₁ hσ₂)) =
        H2π (Rep.trivial (ULift.{u} ℤ) (HomotopyGroup.Pi 1 X p) (ULift.{u} ℤ))
          (torusCycle (ULift.{u} ℤ) (HomotopyGroup.Pi 1 X p)
            (piMap 0 (ContinuousMap.id X) hp (SingularBar.firstAxisClass σ hσ₁))
            (piMap 0 (ContinuousMap.id X) hp (SingularBar.secondAxisClass σ hσ₂))
            ((SingularBar.axisClasses_commute σ hσ₁ hσ₂).map
              (piMap 0 (ContinuousMap.id X) hp))) := by
  subst p
  have hid : piMap 0 (ContinuousMap.id X) (x := σ (0, 0)) rfl =
      MonoidHom.id (HomotopyGroup.Pi 1 X (σ (0, 0))) := by
    apply MonoidHom.ext
    intro a
    exact HomotopyGroup.map_id a
  rw [hid]
  change SingularBar.hTwoMap (σ (0, 0))
    ((SecondHurewicz.Chains X).homologyπ 2 (SingularBar.squareTwoCycle σ hσ₁ hσ₂)) =
      H2π (Rep.trivial (ULift.{u} ℤ) (HomotopyGroup.Pi 1 X (σ (0, 0))) (ULift.{u} ℤ))
        (torusCycle (ULift.{u} ℤ) (HomotopyGroup.Pi 1 X (σ (0, 0)))
          (SingularBar.firstAxisClass σ hσ₁) (SingularBar.secondAxisClass σ hσ₂)
          (SingularBar.axisClasses_commute σ hσ₁ hσ₂))
  exact SingularBar.hTwoMap_squareTwoCycle σ hσ₁ hσ₂

/-- The first named-vertex axis has exactly the class of its supplied original path. -/
theorem firstAxisClass_at_of_edge (σ : C(unitInterval × unitInterval, X))
    (hσ : ∀ t, σ (0, t) = σ (1, t)) {p : X} (hp : σ (0, 0) = p)
    (A : Path p p) (hA : ∀ t, σ (t, 0) = A t) :
    piMap 0 (ContinuousMap.id X) hp (SingularBar.firstAxisClass σ hσ) =
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm (FundamentalGroup.fromPath ⟦A⟧) := by
  rw [firstAxisClass_eq, piMap_id_loopClass]
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [loopClass_toFundamentalGroup, MulEquiv.apply_symm_apply]
  apply End.ext
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact hA t

/-- The second named-vertex axis has exactly the class of its supplied original path. -/
theorem secondAxisClass_at_of_edge (σ : C(unitInterval × unitInterval, X))
    (hσ : ∀ t, σ (t, 0) = σ (t, 1)) {p : X} (hp : σ (0, 0) = p)
    (B : Path p p) (hB : ∀ t, σ (0, t) = B t) :
    piMap 0 (ContinuousMap.id X) hp (SingularBar.secondAxisClass σ hσ) =
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm (FundamentalGroup.fromPath ⟦B⟧) := by
  rw [secondAxisClass_eq, piMap_id_loopClass]
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [loopClass_toFundamentalGroup, MulEquiv.apply_symm_apply]
  apply End.ext
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact hB t

end ModuleCat.FiniteProjective.StableCompletion

namespace ModuleCat.FiniteProjective.StableCompletion
open FundamentalGroupoid.LocalCoefficients groupHomology
open HomotopyFiber.PeriodicConnecting
variable (F : Type u) [Field F] {T : Type (u + 1)} [TopologicalSpace T]
  (q : C(T, ZeroComponent F)) (e : T) (he : q e = stableZeroMap F (stableBase F))
  (hq : IsCoveringMap q) [SimplyConnectedSpace T]

/-- The actual original K-two detector sends the supplied geometric torus to the NEGATIVE
original two-triangle cycle. The sign comes from the original connecting convention. -/
theorem originalKTwoToPullbackHomology_periodic (a b : Fˣ)
    (σ : C(unitInterval × unitInterval, Covering.Pullback.Space (stableZeroMap F) q))
    (β : GenLoop (Fin 2) T e)
    (H : ((Covering.Pullback.lift (stableZeroMap F) q).comp σ).Homotopy (cubeSquare e β))
    (hx : σ (0, 0) = stableZeroCoverPoint F q e he)
    (hσ₁ : ∀ t, σ (0, t) = σ (1, t)) (hσ₂ : ∀ t, σ (t, 0) = σ (t, 1))
    (hH₁ : ∀ s t, H (s, (0, t)) = H (s, (1, t)))
    (hH₂ : ∀ s t, H (s, (t, 0)) = H (s, (t, 1)))
    (hA : coverElementaryEquiv F q e he hq
      (piMap 0 (ContinuousMap.id _) hx (SingularBar.firstAxisClass σ hσ₁)) =
        StableSteinberg.toElementary F (StableSteinberg.h a))
    (hB : coverElementaryEquiv F q e he hq
      (piMap 0 (ContinuousMap.id _) hx (SingularBar.secondAxisClass σ hσ₂)) =
        StableSteinberg.toElementary F (StableSteinberg.h02 b)) :
    originalKTwoToPullbackHomology F q e he hq
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) =
        Multiplicative.ofAdd (-((SecondHurewicz.Chains _).homologyπ 2
          (SingularBar.squareTwoCycle σ hσ₁ hσ₂))) := by
  let k := Covering.Pullback.lift (stableZeroMap F) q
  let z := stableZeroCoverPoint F q e he
  let c := vertexTrackAt k e σ β H z hx
  let α := (pathTransportMulEquiv c 1).symm (Quotient.mk' β)
  have hπ := steinbergKernelToCoverPiTwo_periodic F q e he hq a b σ β H hx
    hσ₁ hσ₂ hH₁ hH₂ hA hB
  rw [← coverPiTwoToOriginalKTwo_steinberg F q e he hq
    (StableSteinberg.torusDefectKernel a b), hπ, originalKTwoToPullbackHomology_cover]
  have hHurewicz : (SecondHurewicz.hom e α⁻¹).toAdd =
      -(SecondHurewicz.hom e (Quotient.mk' β)).toAdd := by
    rw [map_inv]
    change -(SecondHurewicz.hom e α).toAdd = _
    apply congrArg Neg.neg
    have ht := SecondHurewicz.hom_pathTransport c α
    rw [MulEquiv.apply_symm_apply] at ht
    exact (congrArg Multiplicative.toAdd ht).symm
  let H' : (k.comp σ).Homotopy (SecondHurewiczSquare.cubeSquare β) := {
    toContinuousMap := H.toContinuousMap
    map_zero_left := H.apply_zero
    map_one_left := fun x => (H.apply_one x).trans
      (congrArg (fun m : C(unitInterval × unitInterval, T) => m x)
        (cubeSquare_eq_hurewiczSquare β)) }
  have hs := SecondHurewiczSquare.pushforward_squareTwoCycle_eq_hurewicz
    k σ β hσ₁ hσ₂ H' hH₁ hH₂
  have hinv : (coverLiftHomologyIso F q hq 2).inv
      ((SecondHurewicz.hom e (Quotient.mk' β)).toAdd) =
        (SecondHurewicz.Chains _).homologyπ 2 (SingularBar.squareTwoCycle σ hσ₁ hσ₂) := by
    rw [← hs]
    change ((coverLiftHomologyIso F q hq 2).hom ≫
      (coverLiftHomologyIso F q hq 2).inv) _ = _
    rw [Iso.hom_inv_id]
    rfl
  change Multiplicative.ofAdd ((coverLiftHomologyIso F q hq 2).inv
    ((SecondHurewicz.hom e α⁻¹).toAdd)) = _
  rw [hHurewicz, map_neg, hinv]
  rfl

/-- Actual negative central evaluation sends the derived negative square class
to the positive original ordered Steinberg torus defect. -/
theorem originalKTwoKernelDetector_periodic (a b : Fˣ)
    (σ : C(unitInterval × unitInterval, Covering.Pullback.Space (stableZeroMap F) q))
    (β : GenLoop (Fin 2) T e)
    (H : ((Covering.Pullback.lift (stableZeroMap F) q).comp σ).Homotopy (cubeSquare e β))
    (hx : σ (0, 0) = stableZeroCoverPoint F q e he)
    (hσ₁ : ∀ t, σ (0, t) = σ (1, t)) (hσ₂ : ∀ t, σ (t, 0) = σ (t, 1))
    (hH₁ : ∀ s t, H (s, (0, t)) = H (s, (1, t)))
    (hH₂ : ∀ s t, H (s, (t, 0)) = H (s, (t, 1)))
    (hA : coverElementaryEquiv F q e he hq
      (piMap 0 (ContinuousMap.id _) hx (SingularBar.firstAxisClass σ hσ₁)) =
        StableSteinberg.toElementary F (StableSteinberg.h a))
    (hB : coverElementaryEquiv F q e he hq
      (piMap 0 (ContinuousMap.id _) hx (SingularBar.secondAxisClass σ hσ₂)) =
        StableSteinberg.toElementary F (StableSteinberg.h02 b)) :
    originalKTwoKernelDetector F q e he hq
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) =
        StableSteinberg.torusDefectKernel a b := by
  let := stableZeroCoverPullback_pathConnectedSpace F q e he hq
  let E := coverElementaryEquiv F q e he hq
  let p := coverSteinbergProjection F q e he hq
  have ha : p (StableSteinberg.h a) =
      piMap 0 (ContinuousMap.id _) hx (SingularBar.firstAxisClass σ hσ₁) :=
    E.injective ((E.apply_symm_apply _).trans hA.symm)
  have hb : p (StableSteinberg.h02 b) =
      piMap 0 (ContinuousMap.id _) hx (SingularBar.secondAxisClass σ hσ₂) :=
    E.injective ((E.apply_symm_apply _).trans hB.symm)
  change coverCentralEvaluation F q e he hq
    (pullbackSingularToBar F q e he hq
      (originalKTwoToPullbackHomology F q e he hq
        (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)))) = _
  rw [originalKTwoToPullbackHomology_periodic F q e he hq a b σ β H hx
    hσ₁ hσ₂ hH₁ hH₂ hA hB]
  apply Subtype.ext
  change (negativeCentralHomologyEvaluationToKernel p
    (coverSteinbergProjection_surjective F q e he hq)
    (coverSteinbergProjection_central F q e he hq)
      (Multiplicative.ofAdd (SingularBar.hTwoMap (stableZeroCoverPoint F q e he)
        (-((SecondHurewicz.Chains _).homologyπ 2
          (SingularBar.squareTwoCycle σ hσ₁ hσ₂)))))).val = StableSteinberg.torusDefect a b
  rw [map_neg, hTwoMap_squareTwoCycle_at σ hσ₁ hσ₂ (stableZeroCoverPoint F q e he) hx]
  exact (negativeCentralHomologyEvaluationToKernel_neg_torusCycle p
    (coverSteinbergProjection_surjective F q e he hq)
    (coverSteinbergProjection_central F q e he hq) _ _ _
    (StableSteinberg.h a) (StableSteinberg.h02 b) ha hb).trans
      (StableSteinberg.commutator_h_h02 a b)

end ModuleCat.FiniteProjective.StableCompletion

end
