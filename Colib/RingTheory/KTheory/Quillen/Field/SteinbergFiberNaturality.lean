/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.Quillen.Field.SteinbergFiberComparison
public import Colib.GroupTheory.Steinberg.Torus
public import Colib.Topology.ClassifyingSpace.StableCompletionBasedRingNaturality
public import Colib.RingTheory.KTheory.Quillen.ProjectiveCompletionNaturality
public import Colib.RingTheory.KTheory.Quillen.ProjectiveCompletionBasepoint
public import Colib.Topology.HomotopyFiber.HomotopyPiOneNaturality
public import Colib.Topology.ClassifyingSpace.GroupHom

/-!
# Field change for the original Steinberg-kernel comparison

The displayed field map acts on the original stable matrices, telescope,
completion and Steinberg presentation. The actual homotopy-fiber connecting
map and the prescribed basepoint paths are retained.

## Implementation provenance

Adapted from `Quillen/KTheory/Field/SteinbergFiberNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section

noncomputable section
open Topology SSet HomotopyGroup
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
open scoped Topology
namespace ModuleCat.FiniteProjective.StableCompletion
open StableGeneralLinear.GrothendieckModel
variable {F L : Type u} [Field F] [Field L] (f : F →+* L)

/-- The original stable completion maps form the actual ring-change homotopy square. -/
def stableZeroBaseChangeHomotopy :
    ((zeroCompletionBaseChangeMap f).comp (stableZeroMap F)).Homotopy
      ((stableZeroMap L).comp
        (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom) :=
  ((telescopeZeroBaseChangeHomotopy f).compContinuousMap (originalStableToTelescope F)).trans
    ((ContinuousMap.Homotopy.refl (telescopeZeroMap L)).comp
      (originalStableToTelescope_ringMap f).some)

/-- The original completion comparison detects trivial transport around every based loop. -/
theorem zeroCompletion_pathTransport_loop (R : Type u) [Ring R]
    (p : Path (zeroBase R) (zeroBase R)) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent R) (zeroBase R)) :
    pathTransport p (n + 1) a = a := by
  apply (zeroCompletionPositiveKEquiv R n).injective
  rw [zeroCompletionPositiveKEquiv_apply, zeroCompletionPositiveKEquiv_apply]
  change completionPositiveKEquiv Rᵐᵒᵖ (stageObject R 0) n
      (HomotopyGroup.map (pathComponentInclusion (zeroPoint R)) rfl
        (pathTransport p (n + 1) a)) = _
  rw [← pathTransport_naturality]
  exact completionPositiveKEquiv_pathTransport Rᵐᵒᵖ
    (p.map (pathComponentInclusion (zeroPoint R)).continuous) n _

/-- Paths into the original completion basepoint give the same positive-degree transport. -/
theorem zeroCompletion_pathTransport_eq (R : Type u) [Ring R] {x : ZeroComponent R}
    (p q : Path x (zeroBase R)) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent R) x) :
    pathTransport p (n + 1) a = pathTransport q (n + 1) a := by
  have h := zeroCompletion_pathTransport_loop R (q.symm.trans p) n
    (pathTransport q (n + 1) a)
  rw [pathTransport_trans, pathTransport_symm_apply] at h
  exact h

/-- Field change on the actual stable fiber fundamental groups, through the original square. -/
def stableFiberPiOneMap : StableFiberPiOne F →* StableFiberPiOne L :=
  HomotopyFiber.homotopySquarePiOneMap
    (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
    (zeroCompletionBaseChangeMap f) (stableZeroBaseChangeHomotopy f)
    (stableBase F) (stableBase L) (stableRingMap_point f)

/-- The original stable classifying-space projection commutes with the actual fiber map. -/
theorem stableFiberPiOneMap_projection (a : StableFiberPiOne F) :
    stableFiberPiOneProjection L (stableFiberPiOneMap f a) =
      HomotopyGroup.piMap 0 (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
        (stableRingMap_point f) (stableFiberPiOneProjection F a) :=
  HomotopyFiber.homotopySquarePiOneMap_projection
    (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
    (zeroCompletionBaseChangeMap f) (stableZeroBaseChangeHomotopy f)
    (stableBase F) (stableBase L) (stableRingMap_point f) a

/-- The fiber map retains the literal original stable matrix field map. -/
theorem stableFiberPiOneMap_stableGL (a : StableFiberPiOne F) :
    stableFiberToStableGL L (stableFiberPiOneMap f a) =
      StableGeneralLinear.map f (stableFiberToStableGL F a) := by
  apply (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group L)).injective
  change (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group L))
      ((GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group L)).symm
        (stableFiberPiOneProjection L (stableFiberPiOneMap f a))) = _
  rw [MulEquiv.apply_symm_apply, stableFiberPiOneMap_projection]
  have h := GroupoidClassifying.piOneMap_equiv (StableGeneralLinear.map f)
    ((GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).symm
      (stableFiberPiOneProjection F a))
  rw [MulEquiv.apply_symm_apply] at h
  exact h

/-- The actual fiber projection to elementary matrices forms the original field-map square. -/
theorem stableFiberToElementary_naturality :
    (stableFiberToElementary L).comp (stableFiberPiOneMap f) =
      (StableSteinberg.elementaryMap f).comp (stableFiberToElementary F) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  exact stableFiberPiOneMap_stableGL f a

open scoped commutatorElement

/-- The original universal Steinberg lifts commute with the actual fiber map. -/
theorem steinbergToStableFiber_naturality :
    (stableFiberPiOneMap f).comp (steinbergToStableFiber F) =
      (steinbergToStableFiber L).comp (StableSteinberg.map f) := by
  have hp (z : StableSteinberg.Group F) :
      stableFiberToElementary L (stableFiberPiOneMap f (steinbergToStableFiber F z)) =
        StableSteinberg.toElementary L (StableSteinberg.map f z) := by
    exact (DFunLike.congr_fun (stableFiberToElementary_naturality f)
      (steinbergToStableFiber F z)).trans
        ((congrArg (StableSteinberg.elementaryMap f)
          (DFunLike.congr_fun (steinbergToStableFiber_over F) z)).trans
            (DFunLike.congr_fun (StableSteinberg.toElementary_naturality f) z).symm)
  apply PresentedGroup.ext
  rintro ⟨n, i, j, hij, a⟩
  change stableFiberPiOneMap f (steinbergToStableFiber F (StableSteinberg.x F n i j hij a)) =
    steinbergToStableFiber L (StableSteinberg.map f (StableSteinberg.x F n i j hij a))
  rw [StableSteinberg.map_x]
  let r := stableFiberPiOneMap f (steinbergToStableFiber F
    (StableSteinberg.x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a))
  let s := stableFiberPiOneMap f (steinbergToStableFiber F
    (StableSteinberg.x F (n + 1) (Fin.last n) j.castSucc
      (Fin.castSucc_ne_last j).symm 1))
  have hr : stableFiberToElementary L r = StableSteinberg.toElementary L
      (StableSteinberg.x L (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) (f a)) := by
    simpa only [StableSteinberg.map_x] using hp
      (StableSteinberg.x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a)
  have hs : stableFiberToElementary L s = StableSteinberg.toElementary L
      (StableSteinberg.x L (n + 1) (Fin.last n) j.castSucc
        (Fin.castSucc_ne_last j).symm 1) := by
    simpa only [StableSteinberg.map_x, map_one] using hp
      (StableSteinberg.x F (n + 1) (Fin.last n) j.castSucc (Fin.castSucc_ne_last j).symm 1)
  have hL := StableSteinberg.liftToCentralExtension_x L (stableFiberToElementary L)
    (stableFiberToElementary_surjective L) (ker_stableFiberToElementary_le_center L)
    n i j hij (f a) r s hr hs
  change steinbergToStableFiber L (StableSteinberg.x L n i j hij (f a)) = ⁅r, s⁆ at hL
  rw [StableSteinberg.x_eq_commutator_succ F n i j hij a,
    map_commutatorElement, map_commutatorElement]
  exact hL.symm

/-- The raw image-basepoint path is exactly the displayed original homotopy track. -/
def stableFiberBaseChangePath :
    Path (zeroCompletionBaseChangeMap f (stableZeroMap F (stableBase F)))
      (stableZeroMap L (stableBase L)) :=
  ((stableZeroBaseChangeHomotopy f).evalAt (stableBase F)).cast rfl
    (congrArg (stableZeroMap L) (stableRingMap_point f)).symm

/-- Original connecting naturality retains the complete actual field-change square track. -/
theorem stableFiberConnecting_naturality
    (a : HomotopyGroup.Pi 2 (ZeroComponent F) (stableZeroMap F (stableBase F))) :
    stableFiberPiOneMap f (stableFiberConnecting F a) =
      stableFiberConnecting L (pathTransport (stableFiberBaseChangePath f) 2
        (HomotopyGroup.piMap 1 (zeroCompletionBaseChangeMap f) rfl a)) :=
  HomotopyFiber.homotopySquarePiOneMap_connecting
    (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
    (zeroCompletionBaseChangeMap f) (stableZeroBaseChangeHomotopy f)
    (stableBase F) (stableBase L) (stableRingMap_point f) a

private theorem inverseConnecting_naturality (a : (StableSteinberg.toElementary F).ker) :
    pathTransport (stableFiberBaseChangePath f) 2
      (HomotopyGroup.piMap 1 (zeroCompletionBaseChangeMap f) rfl
        ((imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F a))) =
      (imagePiTwoFiberKernelEquiv L).symm
        (steinbergKernelToFiberKernel L (StableSteinberg.toElementaryKernelMap f a)) := by
  apply stableFiberConnecting_injective L
  calc
    _ = stableFiberPiOneMap f
        (stableFiberConnecting F
          ((imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F a))) :=
      (stableFiberConnecting_naturality f _).symm
    _ = stableFiberPiOneMap f (steinbergToStableFiber F a) :=
      congrArg (stableFiberPiOneMap f)
        (imagePiTwoFiberKernelEquiv_symm_apply F (steinbergKernelToFiberKernel F a))
    _ = steinbergToStableFiber L (StableSteinberg.map f a) :=
      DFunLike.congr_fun (steinbergToStableFiber_naturality f) a.val
    _ = _ := (imagePiTwoFiberKernelEquiv_symm_apply L
      (steinbergKernelToFiberKernel L (StableSteinberg.toElementaryKernelMap f a))).symm

/-- Field change preserves the original kernel-to-Pi-two map
and every prescribed correction path. -/
theorem steinbergKernelToCompletionPiTwo_naturality
    (a : (StableSteinberg.toElementary F).ker) :
    pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) 1
      (HomotopyGroup.piMap 1 (zeroCompletionBaseChangeMap f) rfl
        (steinbergKernelToCompletionPiTwo F a)) =
      steinbergKernelToCompletionPiTwo L (StableSteinberg.toElementaryKernelMap f a) := by
  let b := (imagePiTwoFiberKernelEquiv F).symm (steinbergKernelToFiberKernel F a)
  let c := HomotopyGroup.piMap 1 (zeroCompletionBaseChangeMap f) rfl b
  let p := ((basepointPath F).map (zeroCompletionBaseChangeMap f).continuous).trans
    (zeroCompletionBaseChangeBasepointPath f)
  let q := (stableFiberBaseChangePath f).trans (basepointPath L)
  change pathTransport (zeroCompletionBaseChangeBasepointPath f) 2
      (HomotopyGroup.map (zeroCompletionBaseChangeMap f) rfl
        (pathTransport (basepointPath F) 2 b)) =
    pathTransport (basepointPath L) 2
      ((imagePiTwoFiberKernelEquiv L).symm
        (steinbergKernelToFiberKernel L (StableSteinberg.toElementaryKernelMap f a)))
  rw [← pathTransport_naturality, ← pathTransport_trans]
  exact (zeroCompletion_pathTransport_eq L p q 1 c).trans
    ((pathTransport_trans (stableFiberBaseChangePath f) (basepointPath L) 2 c).trans
      (congrArg (pathTransport (basepointPath L) 2) (inverseConnecting_naturality f a)))

/-- The literal existing Steinberg-kernel comparison is natural for original right-module
scalar extension, without an isomorphism or symbol-normalization assertion. -/
theorem steinbergKernelToRightProjectiveKTwo_naturality
    (a : (StableSteinberg.toElementary F).ker) :
    (rightBaseChangeExact f).KMap 2 (steinbergKernelToRightProjectiveKTwo F a) =
      steinbergKernelToRightProjectiveKTwo L (StableSteinberg.toElementaryKernelMap f a) := by
  exact (zeroCompletionPositiveKEquiv_baseChange f 1
    (steinbergKernelToCompletionPiTwo F a)).symm.trans
      (congrArg (zeroCompletionPositiveKEquiv L 1)
        (steinbergKernelToCompletionPiTwo_naturality f a))

/-- The original field-extension K-map square, as an equality of group homomorphisms. -/
theorem steinbergKernelToRightProjectiveKTwo_naturality_hom :
    ((rightBaseChangeExact f).KMap 2).comp (steinbergKernelToRightProjectiveKTwo F) =
      (steinbergKernelToRightProjectiveKTwo L).comp (StableSteinberg.toElementaryKernelMap f) := by
  ext a
  exact steinbergKernelToRightProjectiveKTwo_naturality f a

end ModuleCat.FiniteProjective.StableCompletion
