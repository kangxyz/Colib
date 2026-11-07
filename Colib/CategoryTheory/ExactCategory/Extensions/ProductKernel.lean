/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Extensions.Product
public import Colib.CategoryTheory.ExactCategory.KernelPullback

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/Extensions/ProductKernel.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The kernel of the actual pullback product of extensions -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C) {X : C} (p q : E.ExtensionOver X)
variable (k : E.ExtensionKernelData p) (l : E.ExtensionKernelData q)

/-- The two kernel inclusions give the kernel-sum map into the actual pullback. -/
def extensionProductKernelι : k.obj ⊞ l.obj ⟶ (E.extensionProductObj p q).obj.left :=
  pullback.lift (biprod.fst ≫ k.ι) (biprod.snd ≫ l.ι) (by simp [k.zero, l.zero])

/-- The kernel-sum inclusion is killed by the product deflation. -/
@[reassoc (attr := simp)]
theorem extensionProductKernel_zero :
    E.extensionProductKernelι p q k l ≫ (E.extensionProductObj p q).obj.hom = 0 := by
  simp [extensionProductKernelι, extensionProductObj, Category.assoc, l.zero]

/-- The kernel of the product is genuinely the direct sum of the two kernels. -/
def extensionProductKernelIsLimit :
    IsLimit (KernelFork.ofι (E.extensionProductKernelι p q k l)
      (E.extensionProductKernel_zero p q k l)) := by
  refine KernelFork.IsLimit.ofι _ _ (fun {W} m hm =>
    biprod.lift
      ((k.isLimit E).lift (KernelFork.ofι (m ≫ pullback.fst _ _) ?_))
      ((l.isLimit E).lift (KernelFork.ofι (m ≫ pullback.snd _ _) ?_))) ?_ ?_
  · simpa only [Category.assoc, pullback.condition, extensionProductObj, Over.mk_hom] using hm
  · simpa only [Category.assoc, extensionProductObj, Over.mk_hom] using hm
  · intro W m hm
    apply pullback.hom_ext
    · simp only [extensionProductKernelι, Category.assoc, pullback.lift_fst,
        biprod.lift_fst_assoc]
      exact (k.isLimit E).fac _ WalkingParallelPair.zero
    · simp only [extensionProductKernelι, Category.assoc, pullback.lift_snd,
        biprod.lift_snd_assoc]
      exact (l.isLimit E).fac _ WalkingParallelPair.zero
  · intro W m hm t ht
    apply biprod.hom_ext
    · apply Fork.IsLimit.hom_ext (k.isLimit E)
      have h := congrArg (fun a => a ≫ pullback.fst p.obj.hom q.obj.hom) ht
      simp only [extensionProductKernelι, Category.assoc, pullback.lift_fst] at h
      simp only [biprod.lift_fst, Fork.IsLimit.lift_ι]
      simpa only [KernelFork.ι_ofι, Category.assoc] using h
    · apply Fork.IsLimit.hom_ext (l.isLimit E)
      have h := congrArg (fun a => a ≫ pullback.snd p.obj.hom q.obj.hom) ht
      simp only [extensionProductKernelι, Category.assoc, pullback.lift_snd] at h
      simp only [biprod.lift_snd, Fork.IsLimit.lift_ι]
      simpa only [KernelFork.ι_ofι, Category.assoc] using h

/-- Direct-sum kernel data for the pullback multiplication, with an actual
conflation in the given exact structure. -/
def extensionProductKernelData : E.ExtensionKernelData (E.extensionProductObj p q) where
  obj := k.obj ⊞ l.obj
  ι := E.extensionProductKernelι p q k l
  zero := E.extensionProductKernel_zero p q k l
  conflation := E.conflation_of_deflation_of_isKernel
    (E.extensionProductObj p q).property (E.extensionProductKernelIsLimit p q k l)

end CategoryTheory.ExactCategory.ExactStructure
