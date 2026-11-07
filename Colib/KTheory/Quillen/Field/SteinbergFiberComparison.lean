/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.GroupTheory.Steinberg.Universal
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionKernel
public import Colib.Topology.ClassifyingSpace.Groupoid
public import Colib.Topology.HomotopyFiber.LoopCentrality
public import Colib.KTheory.Quillen.ProjectiveCompletion

/-!
# The actual stable Steinberg group and the original stable completion fiber

Let `f = stableZeroMap F` and `x = stableBase F`. The homotopy fiber is taken over
`f x`, with its canonical constant-path basepoint. Its actual fundamental group
maps onto the original stable elementary subgroup: the homotopy-fiber exact
sequence identifies the image with the kernel of the raw map on Pi one, and the
specified `basepointPath F` transports that kernel to the already proved kernel
of the original based comparison. The projection kernel is central by the actual
loop action on this homotopy fiber.

The universal Steinberg lift therefore gives `steinbergToStableFiber`, with the
original elementary, stable GL, and classifying-space projection equations.
Asphericity of the original stable group classifying space makes the actual
connecting homomorphism injective. Thus `imagePiTwoFiberKernelEquiv` identifies
Pi two at `f x` with the fiber projection kernel.

`steinbergKernelToCompletionPiTwo` restricts the Steinberg lift to its actual
kernel, inverts that connecting isomorphism, and then uses the ORIGINAL
`basepointPath F` at degree two to reach `zeroBase F`. Its composite
`steinbergKernelToRightProjectiveKTwo` has the original Quillen K2 of finite
projective right modules, explicitly `(exactStructure Fᵐᵒᵖ).K 2`, as codomain.

All constructions hold for every field. No simple-connectivity assumption on
the completion target is used. Perfectness of the fiber fundamental group,
surjectivity of the Steinberg lift, a symbol presentation, field naturality and
positive ordered-symbol normalization are separate questions.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Topology SSet HomotopyGroup
namespace ModuleCat.FiniteProjective.StableCompletion
variable (F : Type u) [Field F]

/-- The actual homotopy fiber over the image of the original stable vertex. -/
abbrev StableFiber :=
  HomotopyFiber (stableZeroMap F) (stableZeroMap F (stableBase F))

/-- The canonical constant-path basepoint of the actual homotopy fiber. -/
def stableFiberBase : StableFiber F :=
  HomotopyFiber.basepoint (stableZeroMap F) (stableZeroMap F (stableBase F)) (stableBase F) rfl

/-- The actual fundamental group of the original stable completion fiber. -/
abbrev StableFiberPiOne := HomotopyGroup.Pi 1 (StableFiber F) (stableFiberBase F)

/-- The original fiber projection on fundamental groups. -/
def stableFiberPiOneProjection : StableFiberPiOne F →*
    HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj (StableGeneralLinear.Group F)))
      (stableBase F) :=
  piMap 0 (HomotopyFiber.projection (stableZeroMap F) (stableZeroMap F (stableBase F)))
    (HomotopyFiber.projection_basepoint (stableZeroMap F)
      (stableZeroMap F (stableBase F)) (stableBase F) rfl)

/-- The actual fiber projection, expressed in the original stable matrix group. -/
def stableFiberToStableGL : StableFiberPiOne F →* StableGeneralLinear.Group F :=
  (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).symm.toMonoidHom.comp
    (stableFiberPiOneProjection F)

/-- The specified basepoint transport is an isomorphism, so it preserves and reflects the kernel. -/
lemma stableRawPiOne_eq_one_iff (a : HomotopyGroup.Pi 1
    (ClassifyingSpace (SingleObj (StableGeneralLinear.Group F))) (stableBase F)) :
    piMap 0 (stableZeroMap F) (x := stableBase F) rfl a = 1 ↔ stablePiOneMap F a = 1 := by
  change _ ↔ pathTransportMulEquiv (basepointPath F) 0 _ = 1
  exact (pathTransportMulEquiv (basepointPath F) 0).map_eq_one_iff.symm

/-- Exactness puts every original fiber loop in the actual stable elementary subgroup. -/
lemma stableFiberToStableGL_mem_elementary (a : StableFiberPiOne F) :
    stableFiberToStableGL F a ∈ StableGeneralLinear.elementary F := by
  rw [← ker_stableGroupPiOneMap F]
  change stablePiOneMap F
    ((GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F))
      ((GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).symm
        (stableFiberPiOneProjection F a))) = 1
  rw [MulEquiv.apply_symm_apply]
  apply (stableRawPiOne_eq_one_iff F _).mp
  have h := HomotopyFiber.piMap_range_projection_eq_ker (stableZeroMap F)
    (stableZeroMap F (stableBase F)) (stableBase F) rfl 0
  exact h.le ⟨a, rfl⟩

/-- The original fiber projection corestricted to the actual elementary subgroup. -/
def stableFiberToElementary : StableFiberPiOne F →* StableGeneralLinear.elementary F where
  toFun a := ⟨stableFiberToStableGL F a, stableFiberToStableGL_mem_elementary F a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

/-- Exactness lifts every actual elementary element to a loop in the actual fiber. -/
theorem stableFiberToElementary_surjective : Function.Surjective (stableFiberToElementary F) := by
  intro g
  let e := GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)
  have hg : stablePiOneMap F (e g.val) = 1 := by
    change stableGroupPiOneMap F g.val = 1
    exact (ker_stableGroupPiOneMap F).ge g.property
  have hraw := (stableRawPiOne_eq_one_iff F _).mpr hg
  have hrange : e g.val ∈ (stableFiberPiOneProjection F).range := by
    rw [stableFiberPiOneProjection, HomotopyFiber.piMap_range_projection_eq_ker]
    exact hraw
  obtain ⟨a, ha⟩ := hrange
  refine ⟨a, Subtype.ext ?_⟩
  change e.symm (stableFiberPiOneProjection F a) = g.val
  rw [ha, e.symm_apply_apply]

/-- Corestriction and the original stable group isomorphism preserve the projection kernel. -/
lemma ker_stableFiberToElementary :
    (stableFiberToElementary F).ker = (stableFiberPiOneProjection F).ker := by
  ext a
  change stableFiberToElementary F a = 1 ↔ stableFiberPiOneProjection F a = 1
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    exact (GroupoidClassifying.singleObjPiOneEquiv
      (StableGeneralLinear.Group F)).symm.map_eq_one_iff.mp h'
  · intro h
    apply Subtype.ext
    change (GroupoidClassifying.singleObjPiOneEquiv
      (StableGeneralLinear.Group F)).symm (stableFiberPiOneProjection F a) = 1
    rw [h, map_one]

/-- The actual fiber projection kernel is central, without connectivity hypotheses. -/
theorem ker_stableFiberToElementary_le_center :
    (stableFiberToElementary F).ker ≤ Subgroup.center (StableFiberPiOne F) := by
  rw [ker_stableFiberToElementary]
  exact HomotopyFiber.ker_piOne_projection_le_center (stableZeroMap F)
    (stableZeroMap F (stableBase F)) (stableBase F) rfl

/-- The universal central-extension lift to the actual fiber fundamental group. -/
def steinbergToStableFiber : StableSteinberg.Group F →* StableFiberPiOne F :=
  StableSteinberg.liftToCentralExtension F (stableFiberToElementary F)
    (stableFiberToElementary_surjective F) (ker_stableFiberToElementary_le_center F)

/-- The actual Steinberg lift lies over the original elementary map. -/
theorem steinbergToStableFiber_over :
    (stableFiberToElementary F).comp (steinbergToStableFiber F) = StableSteinberg.toElementary F :=
  StableSteinberg.liftToCentralExtension_over F (stableFiberToElementary F)
    (stableFiberToElementary_surjective F) (ker_stableFiberToElementary_le_center F)

/-- The actual Steinberg lift is uniquely determined by its elementary projection. -/
theorem steinbergToStableFiber_unique (g : StableSteinberg.Group F →* StableFiberPiOne F)
    (hg : (stableFiberToElementary F).comp g = StableSteinberg.toElementary F) :
    g = steinbergToStableFiber F :=
  StableSteinberg.liftToCentralExtension_unique F (stableFiberToElementary F)
    (ker_stableFiberToElementary_le_center F) g _ hg (steinbergToStableFiber_over F)

/-- The lift retains the literal original stable GL homomorphism. -/
theorem steinbergToStableFiber_stableGL :
    (stableFiberToStableGL F).comp (steinbergToStableFiber F) =
      StableSteinberg.toStableGeneralLinear F := by
  apply MonoidHom.ext
  intro a
  exact congrArg Subtype.val
    (congrArg (fun g : StableSteinberg.Group F →* StableGeneralLinear.elementary F => g a)
      (steinbergToStableFiber_over F))

/-- The original projection on Pi one is the original stable GL map followed by the BG
isomorphism. -/
theorem steinbergToStableFiber_projection :
    (stableFiberPiOneProjection F).comp (steinbergToStableFiber F) =
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).toMonoidHom.comp
        (StableSteinberg.toStableGeneralLinear F) := by
  apply MonoidHom.ext
  intro a
  apply (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).symm.injective
  change (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).symm
    (stableFiberPiOneProjection F (steinbergToStableFiber F a)) =
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).symm
        ((GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F))
          (StableSteinberg.toStableGeneralLinear F a))
  rw [MulEquiv.symm_apply_apply]
  exact congrArg (fun g : StableSteinberg.Group F →* StableGeneralLinear.Group F => g a)
    (steinbergToStableFiber_stableGL F)

/-- The original degree-two connecting homomorphism, at the image basepoint. -/
def stableFiberConnecting :
    HomotopyGroup.Pi 2 (ZeroComponent F) (stableZeroMap F (stableBase F)) →*
      StableFiberPiOne F :=
  HomotopyFiber.connectingHom (stableZeroMap F) (stableZeroMap F (stableBase F))
    (stableBase F) rfl 0

/-- The original connecting image is exactly the kernel of the actual map to E. -/
lemma range_stableFiberConnecting :
    (stableFiberConnecting F).range = (stableFiberToElementary F).ker := by
  rw [ker_stableFiberToElementary]
  exact HomotopyFiber.range_connectingHom_eq_ker_projection (stableZeroMap F)
    (stableZeroMap F (stableBase F)) (stableBase F) rfl 0

/-- Asphericity of the original stable group classifying space makes the connecting map
injective. -/
theorem stableFiberConnecting_injective : Function.Injective (stableFiberConnecting F) := by
  apply (stableFiberConnecting F).ker_eq_bot_iff.mp
  rw [stableFiberConnecting, ← HomotopyFiber.range_piMap_eq_ker_connectingHom]
  let : Subsingleton (HomotopyGroup.Pi 2
      (ClassifyingSpace (SingleObj (StableGeneralLinear.Group F))) (stableBase F)) :=
    GroupoidClassifying.singleObj_subsingleton_higher_pi (StableGeneralLinear.Group F) 0
  apply le_antisymm _ bot_le
  rintro a ⟨b, rfl⟩
  change piMap 1 (stableZeroMap F) rfl b = 1
  rw [Subsingleton.elim b 1, map_one]

/-- The actual connecting map identifies Pi two at the image point with the fiber kernel. -/
def imagePiTwoFiberKernelEquiv :
    HomotopyGroup.Pi 2 (ZeroComponent F) (stableZeroMap F (stableBase F)) ≃*
      (stableFiberToElementary F).ker :=
  (MonoidHom.ofInjective (stableFiberConnecting_injective F)).trans
    (MulEquiv.subgroupCongr (range_stableFiberConnecting F))

/-- The kernel isomorphism retains the original connecting homomorphism. -/
lemma imagePiTwoFiberKernelEquiv_apply (a :
    HomotopyGroup.Pi 2 (ZeroComponent F) (stableZeroMap F (stableBase F))) :
    (imagePiTwoFiberKernelEquiv F a : StableFiberPiOne F) = stableFiberConnecting F a := rfl

/-- The inverse kernel isomorphism is an actual inverse to the connecting map. -/
lemma imagePiTwoFiberKernelEquiv_symm_apply (a : (stableFiberToElementary F).ker) :
    stableFiberConnecting F ((imagePiTwoFiberKernelEquiv F).symm a) = a :=
  congrArg Subtype.val ((imagePiTwoFiberKernelEquiv F).apply_symm_apply a)

/-- The actual Steinberg lift restricted to its original elementary-map kernel. -/
def steinbergKernelToFiberKernel :
    (StableSteinberg.toElementary F).ker →* (stableFiberToElementary F).ker where
  toFun a := ⟨steinbergToStableFiber F a, by
    change stableFiberToElementary F (steinbergToStableFiber F a) = 1
    exact (congrArg (fun g : StableSteinberg.Group F →* StableGeneralLinear.elementary F =>
      g a) (steinbergToStableFiber_over F)).trans a.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (steinbergToStableFiber F) a.val b.val)

/-- The actual kernel-to-Pi-two map, using the specified original basepoint path. -/
def steinbergKernelToCompletionPiTwo : (StableSteinberg.toElementary F).ker →*
    HomotopyGroup.Pi 2 (ZeroComponent F) (zeroBase F) :=
  (pathTransportMulEquiv (basepointPath F) 1).toMonoidHom.comp
    ((imagePiTwoFiberKernelEquiv F).symm.toMonoidHom.comp (steinbergKernelToFiberKernel F))

/-- The displayed formula retains the original path, after the inverse connecting map. -/
lemma steinbergKernelToCompletionPiTwo_apply (a : (StableSteinberg.toElementary F).ker) :
    steinbergKernelToCompletionPiTwo F a = pathTransportMulEquiv (basepointPath F) 1
      ((imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F a)) := rfl

/-- Undoing the specified original transport and applying the original boundary recovers the
lift. -/
theorem connecting_steinbergKernelToCompletionPiTwo (a : (StableSteinberg.toElementary F).ker) :
    stableFiberConnecting F ((pathTransportMulEquiv (basepointPath F) 1).symm
      (steinbergKernelToCompletionPiTwo F a)) = steinbergToStableFiber F a := by
  rw [steinbergKernelToCompletionPiTwo_apply, MulEquiv.symm_apply_apply,
    imagePiTwoFiberKernelEquiv_symm_apply]
  rfl

/-- The resulting map to original Quillen K2 of finite projective right F-modules. -/
def steinbergKernelToRightProjectiveKTwo : (StableSteinberg.toElementary F).ker →*
    (exactStructure Fᵐᵒᵖ).K 2 :=
  (zeroCompletionPositiveKEquiv F 1).toMonoidHom.comp (steinbergKernelToCompletionPiTwo F)

/-- The right-module K2 map uses the existing original completion comparison. -/
lemma steinbergKernelToRightProjectiveKTwo_apply (a : (StableSteinberg.toElementary F).ker) :
    steinbergKernelToRightProjectiveKTwo F a =
      zeroCompletionPositiveKEquiv F 1 (steinbergKernelToCompletionPiTwo F a) := rfl

end ModuleCat.FiniteProjective.StableCompletion
