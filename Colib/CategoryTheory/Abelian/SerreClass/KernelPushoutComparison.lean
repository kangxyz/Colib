/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
The ordinary categorical geometry uses native Mathlib maps and independent universes. -/

public import Mathlib.CategoryTheory.Abelian.CommSq

public import Colib.CategoryTheory.Abelian.SerreClass.KernelPushout
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty

/-!
# Ordinary extension pushouts and their actual kernel comparisons

A monomorphism between epimorphisms over one fixed quotient is the actual
pushout of its kernel map. The original prescribed kernel isomorphism gives
the extension comparison and its literal projection formulas.
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

/-- A monomorphism between epimorphisms with fixed quotient is the pushout
of its induced map on kernels. -/
theorem overKernel_mono_isPushout {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] :
    IsPushout (overKernelι X) ((overKernel N).map f) f.left (overKernelι Y) := by
  let k := (overKernel N).map f
  let d := pushout.desc f.left (overKernelι Y) (overKernel_map_isPullback f).w.symm
  have hd : d ≫ Y.hom = kernelPushoutMap X k := by
    apply pushout.hom_ext
    · simp [d, k, Over.w]
    · simp [d, k]
  let g : Over.mk (kernelPushoutMap X k) ⟶ Y := Over.homMk d hd
  have hdm : Mono d := (IsPushout.of_hasPushout (overKernelι X) k).mono_of_isPullback_of_mono
    (overKernel_map_isPullback f).flip d (by simp [d, k]) (by simp [d, k])
  have hgk : (overKernel N).map g = (kernelPushoutIso X k).inv := by
    apply (cancel_mono (overKernelι Y)).1
    rw [(overKernel_map_isPullback g).w]
    apply (cancel_epi (kernelPushoutIso X k).hom).1
    rw [← Category.assoc, kernelPushoutIso_hom_ι]
    simp [g, d, k]
  have : IsIso ((overKernel N).map g) := by rw [hgk]; infer_instance
  have : Mono g.left := hdm
  have : Epi (Over.mk (kernelPushoutMap X k)).hom := kernelPushoutMap_epi X k
  have : IsIso g := over_isIso_of_mono_of_kernel_isIso g
  have : IsIso d := inferInstanceAs (IsIso ((Over.forget N).map g))
  exact (IsPushout.of_hasPushout (overKernelι X) k).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso d)
    (by simp) (by simp [k]) (by simp [d, k]) (by simp [d, k])

/-- A prescribed identification of the target kernel transports the genuine
extension pushout square. -/
theorem overKernel_mono_isPushout_of_iso {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    IsPushout (overKernelι X) i f.left (e.hom ≫ overKernelι Y) := by
  apply (overKernel_mono_isPushout f).of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rw [← h]
    simp
  · simp
  · simp

/-- The explicit kernel-pushout extension is uniquely identified with any
monomorphic extension having its prescribed kernel enlargement. -/
def kernelPushoutComparisonIso {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    Over.mk (kernelPushoutMap X i) ≅ Y := by
  let sq := overKernel_mono_isPushout_of_iso f i e h
  let a := (IsPushout.of_hasPushout (overKernelι X) i).isoIsPushout _ _ sq
  refine Over.isoMk a ?_
  apply pushout.hom_ext
  · simp [a, Over.w]
  · simp [a]

@[reassoc (attr := simp)]
theorem kernelPushoutComparisonIso_inl {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    pushout.inl (overKernelι X) i ≫ (kernelPushoutComparisonIso f i e h).hom.left =
      f.left := by
  simp [kernelPushoutComparisonIso]

@[reassoc (attr := simp)]
theorem kernelPushoutComparisonIso_inr {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    pushout.inr (overKernelι X) i ≫ (kernelPushoutComparisonIso f i e h).hom.left =
      e.hom ≫ overKernelι Y := by
  simp [kernelPushoutComparisonIso]

/-- The comparison acts on the chosen pullback kernels by exactly the
prescribed kernel identification. -/
theorem kernelPushoutComparisonIso_kernel {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    (overKernel N).map (kernelPushoutComparisonIso f i e h).hom =
      (kernelPushoutIso X i).inv ≫ e.hom := by
  apply (cancel_mono (overKernelι Y)).1
  rw [(overKernel_map_isPullback (kernelPushoutComparisonIso f i e h).hom).w]
  apply (cancel_epi (kernelPushoutIso X i).hom).1
  rw [← Category.assoc, kernelPushoutIso_hom_ι]
  simp

end CategoryTheory.Abelian.SerreLocalization
