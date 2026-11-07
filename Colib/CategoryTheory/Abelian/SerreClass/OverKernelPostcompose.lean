/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
The ordinary categorical geometry uses native Mathlib maps and independent universes. -/

public import Colib.CategoryTheory.Abelian.SerreClass.OverKernelBaseChange
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty

/-!
# Actual slice-kernel maps under ordinary postcomposition

Every kernel maps canonically and monomorphically into the kernel of the
composite. The original naturality and cartesian squares hold for all slice
maps, with no invertibility hypothesis on the change of base.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CategoryTheory.Abelian.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every old kernel maps canonically into the kernel of the composite. -/
def overPostcomposeKernelMap {M N : C} (i : M ⟶ N) (X : Over M) :
    (overKernel M).obj X ⟶ (overKernel N).obj ((Over.map i).obj X) :=
  pullback.lift (overKernelι X) 0 (by
    change overKernelι X ≫ (X.hom ≫ i) = 0 ≫ (0 : (0 : C) ⟶ N)
    simp)

@[reassoc (attr := simp)]
lemma overPostcomposeKernelMap_ι {M N : C} (i : M ⟶ N) (X : Over M) :
    overPostcomposeKernelMap i X ≫ overKernelι ((Over.map i).obj X) = overKernelι X :=
  pullback.lift_fst _ _ _

instance overPostcomposeKernelMap_mono {M N : C} (i : M ⟶ N) (X : Over M) :
    Mono (overPostcomposeKernelMap i X) :=
  mono_of_mono_fac (overPostcomposeKernelMap_ι i X)

@[reassoc]
lemma overPostcomposeKernelMap_naturality {M N : C} (i : M ⟶ N)
    {X Y : Over M} (f : X ⟶ Y) :
    (overKernel M).map f ≫ overPostcomposeKernelMap i Y =
      overPostcomposeKernelMap i X ≫ (overKernel N).map ((Over.map i).map f) := by
  apply (cancel_mono (overKernelι ((Over.map i).obj Y))).1
  simp

/-- The kernel inclusions are cartesian along every ordinary slice arrow. -/
theorem overPostcomposeKernelMap_isPullback {M N : C} (i : M ⟶ N)
    {X Y : Over M} (f : X ⟶ Y) :
    IsPullback ((overKernel M).map f) (overPostcomposeKernelMap i X)
      (overPostcomposeKernelMap i Y) ((overKernel N).map ((Over.map i).map f)) := by
  apply IsPullback.of_bot (t := overKernel_map_isPullback ((Over.map i).map f))
  · change IsPullback ((overKernel M).map f)
      (overPostcomposeKernelMap i X ≫ overKernelι ((Over.map i).obj X))
      (overPostcomposeKernelMap i Y ≫ overKernelι ((Over.map i).obj Y)) f.left
    rw [overPostcomposeKernelMap_ι, overPostcomposeKernelMap_ι]
    exact overKernel_map_isPullback f
  · exact overPostcomposeKernelMap_naturality i f

end CategoryTheory.Abelian.SerreLocalization
