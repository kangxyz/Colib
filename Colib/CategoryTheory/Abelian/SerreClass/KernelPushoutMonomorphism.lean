/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
The ordinary categorical geometry uses native Mathlib maps and independent universes. -/

public import Colib.CategoryTheory.Abelian.SerreClass.KernelPushoutComparison
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty

/-!
# Monicity of the actual kernel-pushout extension map

A prescribed monomorphism from the old kernel induces the original monomorphic
map of extension middle objects, with its literal pushout formula.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Abelian.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

instance kernelPushoutOverHom_mono {N : C} (X : Over N) {U : C}
    (i : (overKernel N).obj X ⟶ U) [Mono i] : Mono (kernelPushoutOverHom X i).left :=
  inferInstanceAs (Mono (pushout.inl (overKernelι X) i))

end CategoryTheory.Abelian.SerreLocalization
