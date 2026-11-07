/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.QuillenComparison
public import Colib.KTheory.MilnorK.Steinberg.Surjectivity
public import Colib.KTheory.Quillen.Field.SteinbergFiberSurjectivity

/-!
# Surjectivity of the original Milnor-to-Quillen K-two maps

All-rank kernel generation and actual stable-fiber perfectness prove surjectivity
of the original right-projective and upper finite-module composites over every
field. The maps and their specified SmallModel universe remain unchanged.

Source: the surjectivity clauses of `Quillen/KTheory/Field/MilnorKTwoSurjectivity.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, with genuine native perfectness
and kernel generation discharging both original comparison premises.
-/

@[expose] public noncomputable section
universe u
open ModuleCat.FiniteProjective.StableCompletion
attribute [local instance] StableSteinberg.kernelCommGroup

namespace MilnorKTheory
variable (F : Type u) [Field F]

/-- Every original right-projective Quillen K-two class comes from the original Milnor map. -/
theorem toRightProjectiveKTwo_surjective : Function.Surjective (toRightProjectiveKTwo F) := by
  intro y
  obtain ⟨a, ha⟩ := steinbergKernelToRightProjectiveKTwo_surjective F y.toMul
  obtain ⟨b, hb⟩ := StableSteinberg.KernelGeneration.milnorToKernel_surjective F
    (Additive.ofMul a)
  refine ⟨b, ?_⟩
  rw [toRightProjectiveKTwo_apply, hb]
  exact congrArg Additive.ofMul ha

/-- The actual upper finite-module comparison also retains surjectivity. -/
theorem toUpperModuleKTwo_surjective : Function.Surjective (toUpperModuleKTwo F) := by
  intro y
  obtain ⟨a, ha⟩ := toRightProjectiveKTwo_surjective F
    (Additive.ofMul ((FGModuleCat.rightProjectiveUpperModuleKEquiv F 2).symm y.toMul))
  refine ⟨a, ?_⟩
  rw [toUpperModuleKTwo_apply, ha]
  exact congrArg Additive.ofMul
    ((FGModuleCat.rightProjectiveUpperModuleKEquiv F 2).apply_symm_apply y.toMul)

end MilnorKTheory
