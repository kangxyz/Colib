/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Steinberg.Surjectivity
import Colib.GroupTheory.Steinberg.Universal

noncomputable section

universe u v

open StableSteinberg StableSteinberg.KernelGeneration

variable (F : Type u) [Field F]

-- No characteristic, infinitude or field-size condition is present.
example : defectSubgroup F = (toElementary F).ker := defectSubgroup_eq_kernel F

example : (toElementary F).ker ≤ stage F 2 := kernel_le_stage_two F

example (n : ℕ) (hn : 2 ≤ n) (g : StableSteinberg.Group F)
    (hg : g ∈ stage F (n + 1)) (hk : toElementary F g = 1) : g ∈ stage F n :=
  stage_succ_kernel_descent F n hn g hg hk

attribute [local instance] kernelCommGroup

example : Function.Surjective (milnorToKernel F) := milnorToKernel_surjective F

-- The surjective map is the existing ordered-symbol map, without a second Milnor model.
example (a b : Fˣ) :
    milnorToKernel F (milnorKTupleSymbol ![a, b]) = Additive.ofMul (torusDefectKernel a b) :=
  milnorToKernel_pair a b

-- The central extension may occupy an independent universe.
example {H : Type v} [Group H] (p : H →* StableGeneralLinear.elementary F)
    (hp : Function.Surjective p) (hc : p.ker ≤ Subgroup.center H) :
    ∃! f : StableSteinberg.Group F →* H, p.comp f = toElementary F :=
  existsUnique_lift_toElementary F p hp hc

-- The constructed lift of the original presentation to itself is the identity.
example : liftToCentralExtension F (toElementary F) (toElementary_surjective F)
    (ker_toElementary_le_center F) = MonoidHom.id (StableSteinberg.Group F) := by
  apply liftToCentralExtension_unique F (toElementary F) (ker_toElementary_le_center F)
  · exact liftToCentralExtension_over F _ _ _
  · exact MonoidHom.comp_id _
