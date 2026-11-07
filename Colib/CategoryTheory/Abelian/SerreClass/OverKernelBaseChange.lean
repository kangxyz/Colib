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
# Ordinary change-of-base comparisons for actual slice kernels

Arbitrary base change and monomorphic postcomposition retain the original
kernel isomorphisms and actual counit formulas. Serre-isomorphism stability is
proved for the original base-change maps.
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
@[reassoc (attr := simp)]
lemma overKernel_map_ι {N : C} {X Y : Over N} (f : X ⟶ Y) :
    (overKernel N).map f ≫ overKernelι Y = overKernelι X ≫ f.left :=
  (overKernel_map_isPullback f).w

/-- Naturality of slice pullback is itself an actual pullback square. -/
theorem overBaseChange_map_isPullback {M N : C} (i : M ⟶ N)
    {X Y : Over N} (f : X ⟶ Y) :
    IsPullback ((Over.pullback i).map f).left (pullback.fst X.hom i)
      (pullback.fst Y.hom i) f.left := by
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback Y.hom i).flip)
  · dsimp only [Over.pullback_map_left]
    erw [pullback.lift_snd, Over.w f]
    exact (IsPullback.of_hasPullback X.hom i).flip
  · dsimp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _

/-- The kernel of a base change is the same pullback kernel, via pasting. -/
def overBaseChangeKernelObjIso {M N : C} (i : M ⟶ N) (X : Over N) :
    (overKernel M).obj ((Over.pullback i).obj X) ≅ (overKernel N).obj X := by
  let sq := (IsPullback.of_hasPullback (pullback.snd X.hom i) (0 : (0 : C) ⟶ M)).paste_horiz
    (IsPullback.of_hasPullback X.hom i)
  simp only [zero_comp] at sq
  exact sq.isoPullback

@[reassoc (attr := simp)]
lemma overBaseChangeKernelObjIso_hom_ι {M N : C} (i : M ⟶ N) (X : Over N) :
    (overBaseChangeKernelObjIso i X).hom ≫ overKernelι X =
      overKernelι ((Over.pullback i).obj X) ≫ pullback.fst X.hom i := by
  exact IsPullback.isoPullback_hom_fst _

/-- Taking the kernel commutes naturally with arbitrary change of base. -/
def overBaseChangeKernelIso {M N : C} (i : M ⟶ N) :
    Over.pullback i ⋙ overKernel M ≅ overKernel N :=
  NatIso.ofComponents (overBaseChangeKernelObjIso i) (by
    intro X Y f
    apply (cancel_mono (overKernelι Y)).1
    simp only [Functor.comp_map, Category.assoc, overBaseChangeKernelObjIso_hom_ι,
      overKernel_map_ι_assoc, overKernel_map_ι, overBaseChangeKernelObjIso_hom_ι_assoc]
    rw [(overBaseChange_map_isPullback i f).w])

/-- A monomorphic change of base does not change the kernel object. -/
def overPostcomposeKernelObjIso {M N : C} (i : M ⟶ N) [Mono i] (X : Over M) :
    (overKernel N).obj ((Over.map i).obj X) ≅ (overKernel M).obj X :=
  (overKernelIsKernel ((Over.map i).obj X)).conePointUniqueUpToIso
    (isKernelCompMono (overKernelIsKernel X) i rfl)

@[reassoc (attr := simp)]
lemma overPostcomposeKernelObjIso_hom_ι {M N : C} (i : M ⟶ N) [Mono i] (X : Over M) :
    (overPostcomposeKernelObjIso i X).hom ≫ overKernelι X =
      overKernelι ((Over.map i).obj X) :=
  (overKernelIsKernel ((Over.map i).obj X)).conePointUniqueUpToIso_hom_comp
    (isKernelCompMono (overKernelIsKernel X) i rfl) .zero

/-- The postcomposition comparison of kernels is natural on ordinary slice maps. -/
def overPostcomposeKernelIso {M N : C} (i : M ⟶ N) [Mono i] :
    Over.map i ⋙ overKernel N ≅ overKernel M :=
  NatIso.ofComponents (overPostcomposeKernelObjIso i) (by
    intro X Y f
    apply (cancel_mono (overKernelι Y)).1
    simp only [Category.assoc, overPostcomposeKernelObjIso_hom_ι]
    rw [(overKernel_map_isPullback f).w]
    rw [← Category.assoc, overPostcomposeKernelObjIso_hom_ι]
    exact (overKernel_map_isPullback ((Over.map i).map f)).w)

/-- The canonical pullback inclusion is monic when the change of base is. -/
instance overBaseChangeCounit_mono {M N : C} (i : M ⟶ N) [Mono i] (X : Over N) :
    Mono ((Over.mapPullbackAdj i).counit.app X).left := by
  simpa only [Over.mapPullbackAdj_counit_app] using
    (inferInstanceAs (Mono (pullback.fst X.hom i)))

/-- The pullback counit's map on kernels is the composite of the two
canonical change-of-base identifications. -/
lemma overBaseChangeCounit_kernel {M N : C} (i : M ⟶ N) [Mono i] (X : Over N) :
    (overKernel N).map ((Over.mapPullbackAdj i).counit.app X) =
      (overPostcomposeKernelObjIso i ((Over.pullback i).obj X)).hom ≫
        (overBaseChangeKernelObjIso i X).hom := by
  apply (cancel_mono (overKernelι X)).1
  calc
    _ = overKernelι ((Over.map i).obj ((Over.pullback i).obj X)) ≫ pullback.fst X.hom i := by
      simp [Over.mapPullbackAdj_counit_app]
    _ = _ := by
      simp only [Category.assoc, overBaseChangeKernelObjIso_hom_ι,
        overPostcomposeKernelObjIso_hom_ι_assoc]

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- Pullback retains the Serre-isomorphism condition on the structure map. -/
theorem overBaseChange_isoModSerre {M N : C} (i : M ⟶ N) (X : Over N)
    (hX : P.isoModSerre X.hom) : P.isoModSerre ((Over.pullback i).obj X).hom :=
  MorphismProperty.of_isPullback (P := P.isoModSerre)
    (IsPullback.of_hasPullback X.hom i) hX

end CategoryTheory.Abelian.SerreLocalization
