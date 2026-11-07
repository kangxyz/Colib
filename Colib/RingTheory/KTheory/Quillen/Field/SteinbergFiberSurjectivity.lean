/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.GroupTheory.MonoidHom.CentralLifts
public import Colib.RingTheory.KTheory.Quillen.Field.SteinbergFiberComparison
public import Colib.RingTheory.KTheory.Quillen.StableFiberPerfectness

/-!
# Surjectivity of the original Steinberg-to-Quillen maps

The actual stable fiber has perfect fundamental group by native cap descent.
The original central lift is therefore surjective, as are its kernel restriction,
the inverse connecting map, the specified basepoint transport, and the original
right-projective Quillen K-two comparison. No perfectness premise remains.

Source: `Quillen/KTheory/Field/SteinbergFiberSurjectivity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with its perfectness premise discharged
by the genuine native `stableZeroFiber_piOne_isPerfect` theorem.
-/
@[expose] public section

noncomputable section

universe u
open Topology
namespace ModuleCat.FiniteProjective.StableCompletion
variable (F : Type u) [Field F]

/-- The original Steinberg lift is surjective using perfectness of its actual fiber target. -/
theorem steinbergToStableFiber_surjective :
    Function.Surjective (steinbergToStableFiber F) := by
  let : Group.IsPerfect (StableFiberPiOne F) := stableZeroFiber_piOne_isPerfect F
  apply MonoidHom.surjective_of_central_ker_of_surjective_comp
    (steinbergToStableFiber F) (stableFiberToElementary F)
    (ker_stableFiberToElementary_le_center F)
  rw [steinbergToStableFiber_over]
  exact StableSteinberg.toElementary_surjective F

/-- The same original lift restricts surjectively to the original elementary-map kernel. -/
theorem steinbergKernelToFiberKernel_surjective :
    Function.Surjective (steinbergKernelToFiberKernel F) := by
  intro a
  obtain ⟨b, hb⟩ := steinbergToStableFiber_surjective F (a : StableFiberPiOne F)
  have hk : b ∈ (StableSteinberg.toElementary F).ker := by
    change StableSteinberg.toElementary F b = 1
    rw [← steinbergToStableFiber_over]
    change stableFiberToElementary F (steinbergToStableFiber F b) = 1
    rw [hb]
    exact a.property
  exact ⟨⟨b, hk⟩, Subtype.ext hb⟩

/-- The original inverse connecting map and specified basepoint transport preserve surjectivity. -/
theorem steinbergKernelToCompletionPiTwo_surjective :
    Function.Surjective (steinbergKernelToCompletionPiTwo F) :=
  (pathTransportMulEquiv (basepointPath F) 1).surjective.comp
    ((imagePiTwoFiberKernelEquiv F).symm.surjective.comp
      (steinbergKernelToFiberKernel_surjective F))

/-- The original right-projective Quillen K2 map is surjective without further hypotheses. -/
theorem steinbergKernelToRightProjectiveKTwo_surjective :
    Function.Surjective (steinbergKernelToRightProjectiveKTwo F) :=
  (zeroCompletionPositiveKEquiv F 1).surjective.comp
    (steinbergKernelToCompletionPiTwo_surjective F)

end ModuleCat.FiniteProjective.StableCompletion
