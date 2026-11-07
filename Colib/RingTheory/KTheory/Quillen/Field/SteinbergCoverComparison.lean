/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.Quillen.StableZeroFiberGeometry
public import Colib.Topology.Covering.HomotopyGroups
public import Colib.RepresentationTheory.Homological.GroupHomology.Torus
public import Colib.RingTheory.KTheory.Quillen.Field.SteinbergFiberComparison
public import Colib.Topology.LocalCoefficients.SecondHurewicz
public import Colib.Topology.LocalCoefficients.SingularBar
public import Colib.GroupTheory.Steinberg.KernelGeneration
public import Colib.RingTheory.KTheory.MilnorK.Steinberg

/-!
# The original right-projective K2 detector and cover comparison

The original chains, signs, maps, basepoints and stated hypotheses are retained.
-/
/-! Implementation source: `Quillen/KTheory/Field/SteinbergCoverComparison.lean` and
the first-projection equivalence of `Quillen/KTheory/Plus/StablePullbackSchur.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The former IntegralBar/Schur
construction is replaced by evaluation in actual native group homology of the
actual pulled-back central surjection. The original Quillen maps are retained.
-/
@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Topology HomotopyGroup
namespace ModuleCat.FiniteProjective.StableCompletion
open FundamentalGroupoid.LocalCoefficients
variable (F : Type u) [Field F] {T : Type (u + 1)} [TopologicalSpace T]
  (q : C(T, ZeroComponent F)) (e : T) (he : q e = stableZeroMap F (stableBase F))
  (hq : IsCoveringMap q)

include hq in
/-- The original cover-lift chain quasi-isomorphism induces the actual constant-coefficient
homology isomorphism, through the original constant-chain naturality square. -/
theorem coverLiftHomologyMap_isIso (n : ℕ) :
    IsIso (pushforwardHomologyMap (Covering.Pullback.lift (stableZeroMap F) q)
      (constant T integralCoefficients.{u + 1}) n) := by
  let k := Covering.Pullback.lift (stableZeroMap F) q
  let V := integralCoefficients.{u + 1}
  let s := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u + 1} ℤ)).obj V).map
    (TopCat.ofHom k)
  let : QuasiIso s := stableZeroCoverLift_quasiIso F q hq
  have : IsIso ((HomologicalComplex.homologyFunctor _ _ n).map s) := by
    change IsIso (HomologicalComplex.homologyMap s n)
    infer_instance
  have hn := congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ n).map φ)
    (constantChainComplexIso_naturality k V)
  simp only [Functor.map_comp] at hn
  change pushforwardHomologyMap k (constant T V) n ≫ (constantHomologyIso V n).hom =
    (constantHomologyIso V n).hom ≫ (HomologicalComplex.homologyFunctor _ _ n).map s at hn
  have : IsIso (pushforwardHomologyMap k (constant T V) n ≫
      (constantHomologyIso V n).hom) := by
    rw [hn]
    infer_instance
  exact (isIso_comp_right_iff _ (constantHomologyIso V n).hom).mp inferInstance

/-- Inverting this specified isomorphism inverts the actual original map of homology. -/
def coverLiftHomologyIso (n : ℕ) :
    homology (constant (Covering.Pullback.Space (stableZeroMap F) q)
      integralCoefficients.{u + 1}) n ≅
        homology (constant T integralCoefficients.{u + 1}) n := by
  letI := coverLiftHomologyMap_isIso F q hq n
  exact asIso (pushforwardHomologyMap (Covering.Pullback.lift (stableZeroMap F) q)
    (constant T integralCoefficients.{u + 1}) n)

/-- The chosen isomorphism has precisely the original pushforward as its forward map. -/
theorem coverLiftHomologyIso_hom (n : ℕ) :
    (coverLiftHomologyIso F q hq n).hom =
      pushforwardHomologyMap (Covering.Pullback.lift (stableZeroMap F) q)
        (constant T integralCoefficients.{u + 1}) n := rfl

/-- The original covering projection gives the actual Pi-two equivalence at its supplied point. -/
def coverPiTwoEquiv : HomotopyGroup.Pi 2 T e ≃*
    HomotopyGroup.Pi 2 (ZeroComponent F) (stableZeroMap F (stableBase F)) :=
  hq.piProjectionEquiv 0 e he

/-- The original raw Pi-two class has an actual marked homology class in the cover pullback.
This definition asserts no transgression or injectivity law. -/
def rawPiTwoToPullbackHomology :
    HomotopyGroup.Pi 2 (ZeroComponent F) (stableZeroMap F (stableBase F)) →*
      Multiplicative (homology (constant (Covering.Pullback.Space (stableZeroMap F) q)
        integralCoefficients.{u + 1}) 2) :=
  (coverLiftHomologyIso F q hq 2).symm.toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp
    ((SecondHurewicz.hom e).comp (coverPiTwoEquiv F q e he hq).symm.toMonoidHom)

/-- The detector on original right-projective K-two retains both original inverse transports. -/
def originalKTwoToPullbackHomology : (exactStructure Fᵐᵒᵖ).K 2 →*
    Multiplicative (homology (constant (Covering.Pullback.Space (stableZeroMap F) q)
      integralCoefficients.{u + 1}) 2) :=
  (rawPiTwoToPullbackHomology F q e he hq).comp
    ((pathTransportMulEquiv (basepointPath F) 1).symm.toMonoidHom.comp
      (zeroCompletionPositiveKEquiv F 1).symm.toMonoidHom)

/-- On the ORIGINAL Steinberg kernel comparison, precisely those original transports cancel. -/
theorem originalKTwoToPullbackHomology_steinberg (a : (StableSteinberg.toElementary F).ker) :
    originalKTwoToPullbackHomology F q e he hq
      (steinbergKernelToRightProjectiveKTwo F a) =
        rawPiTwoToPullbackHomology F q e he hq
          ((imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F a)) := by
  change rawPiTwoToPullbackHomology F q e he hq
    ((pathTransportMulEquiv (basepointPath F) 1).symm
      ((zeroCompletionPositiveKEquiv F 1).symm
        (zeroCompletionPositiveKEquiv F 1
          (pathTransportMulEquiv (basepointPath F) 1
            ((imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F a)))))) = _
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

end ModuleCat.FiniteProjective.StableCompletion

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Topology HomotopyGroup
namespace ModuleCat.FiniteProjective.StableCompletion
open FundamentalGroupoid.LocalCoefficients
variable (F : Type u) [Field F] {T : Type (u + 1)} [TopologicalSpace T]
  (q : C(T, ZeroComponent F)) (e : T) (he : q e = stableZeroMap F (stableBase F))
  (hq : IsCoveringMap q)

/-- The original cover Pi-two class enters original Quillen K-two through the specified maps. -/
def coverPiTwoToOriginalKTwo : HomotopyGroup.Pi 2 T e →* (exactStructure Fᵐᵒᵖ).K 2 :=
  (zeroCompletionPositiveKEquiv F 1).toMonoidHom.comp
    ((pathTransportMulEquiv (basepointPath F) 1).toMonoidHom.comp (piMap 1 q he))

/-- On a cover class, the original inverse transports and actual cover inverse cancel. -/
theorem originalKTwoToPullbackHomology_cover (a : HomotopyGroup.Pi 2 T e) :
    originalKTwoToPullbackHomology F q e he hq (coverPiTwoToOriginalKTwo F q e he a) =
      Multiplicative.ofAdd ((coverLiftHomologyIso F q hq 2).inv
        ((SecondHurewicz.hom e a).toAdd)) := by
  change rawPiTwoToPullbackHomology F q e he hq
    ((pathTransportMulEquiv (basepointPath F) 1).symm
      ((zeroCompletionPositiveKEquiv F 1).symm
        (zeroCompletionPositiveKEquiv F 1
          (pathTransportMulEquiv (basepointPath F) 1 (piMap 1 q he a))))) = _
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  change Multiplicative.ofAdd ((coverLiftHomologyIso F q hq 2).inv
    ((SecondHurewicz.hom e
      ((coverPiTwoEquiv F q e he hq).symm (coverPiTwoEquiv F q e he hq a))).toAdd)) = _
  rw [MulEquiv.symm_apply_apply]

variable [SimplyConnectedSpace T]

/-- The actual cover pullback Pi one is identified with the elementary subgroup
through its original first projection and stable classifying-space equivalence. -/
def coverElementaryEquiv :
    HomotopyGroup.Pi 1 (Covering.Pullback.Space (stableZeroMap F) q)
      (stableZeroCoverPoint F q e he) ≃* StableGeneralLinear.elementary F := by
  let c := Covering.Pullback.piOneKernelEquiv (stableZeroMap F) q hq
    (stableZeroCoverPoint F q e he)
  have hk : (piMap 0 (stableZeroMap F) (stableZeroCoverPoint F q e he).property).ker =
      (StableGeneralLinear.elementary F).map
        (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).toMonoidHom :=
    by
      have hraw (y : ZeroComponent F) (h : stableZeroMap F (stableBase F) = y) :
          (piMap 0 (stableZeroMap F) h).ker = (StableGeneralLinear.elementary F).map
            (GroupoidClassifying.singleObjPiOneEquiv
              (StableGeneralLinear.Group F)).toMonoidHom := by
        subst y
        exact stableZeroMap_rawPiOne_kernel F
      exact hraw (q e) he.symm
  exact (c.trans (MulEquiv.subgroupCongr hk)).trans
    ((GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).subgroupMap
      (StableGeneralLinear.elementary F)).symm

/-- The displayed identification retains the original based first-projection map. -/
theorem coverElementaryEquiv_apply
    (a : HomotopyGroup.Pi 1 (Covering.Pullback.Space (stableZeroMap F) q)
      (stableZeroCoverPoint F q e he)) :
    (coverElementaryEquiv F q e he hq a : StableGeneralLinear.Group F) =
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).symm
        (piMap 0 (Covering.Pullback.projection (stableZeroMap F) q)
          (x := stableZeroCoverPoint F q e he) rfl a) := rfl

/-- The original Steinberg central surjection, transported only in its target group. -/
def coverSteinbergProjection : StableSteinberg.Group F →*
    HomotopyGroup.Pi 1 (Covering.Pullback.Space (stableZeroMap F) q)
      (stableZeroCoverPoint F q e he) :=
  (coverElementaryEquiv F q e he hq).symm.toMonoidHom.comp (StableSteinberg.toElementary F)

/-- The actual transported projection is surjective. -/
theorem coverSteinbergProjection_surjective :
    Function.Surjective (coverSteinbergProjection F q e he hq) :=
  (coverElementaryEquiv F q e he hq).symm.surjective.comp
    (StableSteinberg.toElementary_surjective F)

/-- Transporting the target retains exactly the original Steinberg kernel. -/
theorem coverSteinbergProjection_ker :
    (coverSteinbergProjection F q e he hq).ker = (StableSteinberg.toElementary F).ker := by
  ext a
  exact (coverElementaryEquiv F q e he hq).symm.map_eq_one_iff

/-- The original centrality theorem applies to this same kernel. -/
theorem coverSteinbergProjection_central :
    (coverSteinbergProjection F q e he hq).ker ≤ Subgroup.center (StableSteinberg.Group F) := by
  rw [coverSteinbergProjection_ker]
  exact StableSteinberg.ker_toElementary_le_center F

/-- The actual singular-to-bar homomorphism uses the literal pullback fundamental group. -/
def pullbackSingularToBar :
    Multiplicative (homology (constant (Covering.Pullback.Space (stableZeroMap F) q)
      integralCoefficients.{u + 1}) 2) →*
        Multiplicative (groupHomology.H2 (Rep.trivial (ULift.{u + 1} ℤ) (HomotopyGroup.Pi 1
          (Covering.Pullback.Space (stableZeroMap F) q) (stableZeroCoverPoint F q e he))
            (ULift.{u + 1} ℤ))) := by
  letI := stableZeroCoverPullback_pathConnectedSpace F q e he hq
  exact (SingularBar.hTwoMap (stableZeroCoverPoint F q e he)).hom.toAddMonoidHom.toMultiplicative

/-- The native group-H-two homomorphism on original right-projective Quillen K-two. -/
def originalKTwoToNativeH2 : (exactStructure Fᵐᵒᵖ).K 2 →*
    Multiplicative (groupHomology.H2 (Rep.trivial (ULift.{u + 1} ℤ) (HomotopyGroup.Pi 1
      (Covering.Pullback.Space (stableZeroMap F) q) (stableZeroCoverPoint F q e he))
        (ULift.{u + 1} ℤ))) :=
  (pullbackSingularToBar F q e he hq).comp (originalKTwoToPullbackHomology F q e he hq)

/-- Native negative central evaluation takes values in the original Steinberg kernel.
No Schur equivalence or perfect-group homology comparison is used. -/
def coverCentralEvaluation :
    Multiplicative (groupHomology.H2 (Rep.trivial (ULift.{u + 1} ℤ)
      (HomotopyGroup.Pi 1 (Covering.Pullback.Space (stableZeroMap F) q)
        (stableZeroCoverPoint F q e he)) (ULift.{u + 1} ℤ))) →*
      (StableSteinberg.toElementary F).ker :=
  (MulEquiv.subgroupCongr (coverSteinbergProjection_ker F q e he hq)).toMonoidHom.comp
    (groupHomology.negativeCentralHomologyEvaluationToKernel
      (coverSteinbergProjection F q e he hq)
      (coverSteinbergProjection_surjective F q e he hq)
      (coverSteinbergProjection_central F q e he hq))

/-- The actual homomorphism from original Quillen K-two to the original Steinberg kernel.
The separate geometric calibration must still prove its left-inverse identity. -/
def originalKTwoKernelDetector : (exactStructure Fᵐᵒᵖ).K 2 →*
    (StableSteinberg.toElementary F).ker :=
  (coverCentralEvaluation F q e he hq).comp (originalKTwoToNativeH2 F q e he hq)

/-- The exact original-comparison input retains its actual inverse connecting class. -/
theorem originalKTwoToNativeH2_steinberg (a : (StableSteinberg.toElementary F).ker) :
    originalKTwoToNativeH2 F q e he hq (steinbergKernelToRightProjectiveKTwo F a) =
      pullbackSingularToBar F q e he hq
        (rawPiTwoToPullbackHomology F q e he hq
          ((imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F a))) := by
  change pullbackSingularToBar F q e he hq
    (originalKTwoToPullbackHomology F q e he hq (steinbergKernelToRightProjectiveKTwo F a)) = _
  rw [originalKTwoToPullbackHomology_steinberg]

end ModuleCat.FiniteProjective.StableCompletion

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory Topology HomotopyGroup
open scoped commutatorElement
namespace ModuleCat.FiniteProjective.StableCompletion

/-- Proved original kernel generation gives extensionality on the original ordered defects. -/
theorem kernelHom_ext_torusDefect (F : Type u) [Field F] {A : Type v} [Group A]
    (f g : (StableSteinberg.toElementary F).ker →* A)
    (h : ∀ a b : Fˣ, f (StableSteinberg.torusDefectKernel a b) =
      g (StableSteinberg.torusDefectKernel a b)) : f = g := by
  let S := (StableSteinberg.toElementary F).ker
  have hs : StableSteinberg.KernelGeneration.defectSubgroup F ≤
      (f.eqLocus g).map S.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro a ⟨r, s, rfl⟩
    exact ⟨StableSteinberg.torusDefectKernel r s, h r s, rfl⟩
  apply MonoidHom.ext
  intro a
  have ha : (a : StableSteinberg.Group F) ∈
      StableSteinberg.KernelGeneration.defectSubgroup F :=
    (StableSteinberg.KernelGeneration.defectSubgroup_eq_kernel F).symm ▸ a.property
  obtain ⟨b, hb, he⟩ := hs ha
  have he' : b = a := Subtype.ext he
  change f b = g b at hb
  exact he' ▸ hb

end ModuleCat.FiniteProjective.StableCompletion

namespace ModuleCat.FiniteProjective.StableCompletion
open FundamentalGroupoid.LocalCoefficients
variable (F : Type u) [Field F] {T : Type (u + 1)} [TopologicalSpace T]
  (q : C(T, ZeroComponent F)) (e : T) (he : q e = stableZeroMap F (stableBase F))
  (hq : IsCoveringMap q) [SimplyConnectedSpace T]

/-- The literal fundamental group of the actual cover-lift fiber at its constant-path point. -/
abbrev CoverFiberPiOne := HomotopyGroup.Pi 1
  (HomotopyFiber (Covering.Pullback.lift (stableZeroMap F) q) e)
  (HomotopyFiber.basepoint (Covering.Pullback.lift (stableZeroMap F) q) e
    (stableZeroCoverPoint F q e he) rfl)

/-- The original fiber projection into the actual pullback fundamental group. -/
def coverFiberProjection : CoverFiberPiOne F q e he →*
    HomotopyGroup.Pi 1 (Covering.Pullback.Space (stableZeroMap F) q)
      (stableZeroCoverPoint F q e he) :=
  piMap 0 (HomotopyFiber.projection (Covering.Pullback.lift (stableZeroMap F) q) e) rfl

/-- The ORIGINAL Steinberg map transported by the actual cover-fiber equivalence. -/
def steinbergToCoverFiber : StableSteinberg.Group F →* CoverFiberPiOne F q e he :=
  (stableZeroCoverFiberPiOneEquiv F q e he hq).symm.toMonoidHom.comp (steinbergToStableFiber F)

/-- Forward cover-fiber transport recovers the original Steinberg map exactly. -/
theorem coverFiberEquiv_steinberg (a : StableSteinberg.Group F) :
    stableZeroCoverFiberPiOneEquiv F q e he hq (steinbergToCoverFiber F q e he hq a) =
      steinbergToStableFiber F a :=
  (stableZeroCoverFiberPiOneEquiv F q e he hq).apply_symm_apply _

/-- The original elementary projection survives both the cover and fiber transports. -/
theorem steinbergToCoverFiber_over :
    (coverElementaryEquiv F q e he hq).toMonoidHom.comp
      ((coverFiberProjection F q e he).comp (steinbergToCoverFiber F q e he hq)) =
        StableSteinberg.toElementary F := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  change (coverElementaryEquiv F q e he hq
    (coverFiberProjection F q e he (steinbergToCoverFiber F q e he hq a)) :
      StableGeneralLinear.Group F) = _
  rw [coverElementaryEquiv_apply]
  have h := congrArg (fun k => k (steinbergToCoverFiber F q e he hq a))
    (stableZeroCoverFiberPiOneMap_projection F q e he)
  change stableFiberPiOneProjection F
      (stableZeroCoverFiberPiOneEquiv F q e he hq (steinbergToCoverFiber F q e he hq a)) =
    piMap 0 (Covering.Pullback.projection (stableZeroMap F) q) rfl
      (coverFiberProjection F q e he (steinbergToCoverFiber F q e he hq a)) at h
  rw [coverFiberEquiv_steinberg] at h
  rw [← h]
  exact congrArg Subtype.val
    (congrArg (fun k => k a) (steinbergToStableFiber_over F))

/-- The actual original kernel Pi-two class, lifted through the actual cover equivalence. -/
def steinbergKernelToCoverPiTwo : (StableSteinberg.toElementary F).ker →*
    HomotopyGroup.Pi 2 T e :=
  (coverPiTwoEquiv F q e he hq).symm.toMonoidHom.comp
    ((imagePiTwoFiberKernelEquiv F).symm.toMonoidHom.comp (steinbergKernelToFiberKernel F))

/-- The ORIGINAL connecting map sends the exact class to the transported Steinberg lift. -/
theorem connecting_steinbergKernelToCoverPiTwo (a : (StableSteinberg.toElementary F).ker) :
    HomotopyFiber.connectingHom (Covering.Pullback.lift (stableZeroMap F) q) e
      (stableZeroCoverPoint F q e he) rfl 0 (steinbergKernelToCoverPiTwo F q e he hq a) =
        steinbergToCoverFiber F q e he hq a := by
  apply (stableZeroCoverFiberPiOneEquiv F q e he hq).injective
  rw [coverFiberEquiv_steinberg]
  have h := congrArg (fun k => k (steinbergKernelToCoverPiTwo F q e he hq a))
    (stableZeroCoverFiberPiOneMap_connecting F q e he)
  change stableZeroCoverFiberPiOneEquiv F q e he hq
      (HomotopyFiber.connectingHom (Covering.Pullback.lift (stableZeroMap F) q) e
        (stableZeroCoverPoint F q e he) rfl 0 (steinbergKernelToCoverPiTwo F q e he hq a)) =
    stableFiberConnecting F
      (coverPiTwoEquiv F q e he hq (steinbergKernelToCoverPiTwo F q e he hq a)) at h
  rw [h]
  change stableFiberConnecting F (coverPiTwoEquiv F q e he hq
    ((coverPiTwoEquiv F q e he hq).symm
      ((imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F a)))) = _
  rw [MulEquiv.apply_symm_apply, imagePiTwoFiberKernelEquiv_symm_apply]
  rfl

omit [SimplyConnectedSpace T] in
/-- The cover class maps back to the ORIGINAL right-projective K-two comparison. -/
theorem coverPiTwoToOriginalKTwo_steinberg (a : (StableSteinberg.toElementary F).ker) :
    coverPiTwoToOriginalKTwo F q e he (steinbergKernelToCoverPiTwo F q e he hq a) =
      steinbergKernelToRightProjectiveKTwo F a := by
  change zeroCompletionPositiveKEquiv F 1
    (pathTransportMulEquiv (basepointPath F) 1
      (coverPiTwoEquiv F q e he hq ((coverPiTwoEquiv F q e he hq).symm
        ((imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F a))))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

omit [SimplyConnectedSpace T] in
include hq in
/-- The actual cover connecting map is injective by the ORIGINAL stable connecting map. -/
theorem coverConnecting_injective : Function.Injective
    (HomotopyFiber.connectingHom (Covering.Pullback.lift (stableZeroMap F) q) e
      (stableZeroCoverPoint F q e he) rfl 0) := by
  intro a b hab
  apply (coverPiTwoEquiv F q e he hq).injective
  apply stableFiberConnecting_injective F
  have h := stableZeroCoverFiberPiOneMap_connecting F q e he
  have ha := congrArg (fun k => k a) h
  have hb := congrArg (fun k => k b) h
  change _ = stableFiberConnecting F (coverPiTwoEquiv F q e he hq a) at ha
  change _ = stableFiberConnecting F (coverPiTwoEquiv F q e he hq b) at hb
  exact ha.symm.trans ((congrArg (stableZeroCoverFiberPiOneMap F q e he) hab).trans hb)

omit [SimplyConnectedSpace T] in
/-- The literal cover-fiber projection has its proved actual central kernel. -/
theorem coverFiberProjection_central :
    (coverFiberProjection F q e he).ker ≤ Subgroup.center (CoverFiberPiOne F q e he) :=
  HomotopyFiber.ker_piOne_projection_le_center (Covering.Pullback.lift (stableZeroMap F) q)
    e (stableZeroCoverPoint F q e he) rfl

/-- Any geometric axis lifts with the original elementary projections compute the ORIGINAL
Steinberg torus defect. Their individual stored fiber paths need not be the chosen lifts. -/
theorem steinbergToCoverFiber_torusDefect (a b : Fˣ) (A B : CoverFiberPiOne F q e he)
    (hA : coverElementaryEquiv F q e he hq (coverFiberProjection F q e he A) =
      StableSteinberg.toElementary F (StableSteinberg.h a))
    (hB : coverElementaryEquiv F q e he hq (coverFiberProjection F q e he B) =
      StableSteinberg.toElementary F (StableSteinberg.h02 b)) :
    steinbergToCoverFiber F q e he hq (StableSteinberg.torusDefect a b) = ⁅A, B⁆ := by
  rw [← StableSteinberg.commutator_h_h02, map_commutatorElement]
  apply MonoidHom.CentralKernel.commutator_eq_of_projection_eq (coverFiberProjection F q e he)
    (coverFiberProjection_central F q e he)
  · apply (coverElementaryEquiv F q e he hq).injective
    exact (congrArg (fun k => k (StableSteinberg.h a))
      (steinbergToCoverFiber_over F q e he hq)).trans hA.symm
  · apply (coverElementaryEquiv F q e he hq).injective
    exact (congrArg (fun k => k (StableSteinberg.h02 b))
      (steinbergToCoverFiber_over F q e he hq)).trans hB.symm

end ModuleCat.FiniteProjective.StableCompletion

end
