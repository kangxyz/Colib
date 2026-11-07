/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionConnected
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionProductCoordinates

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionDiagonal.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The natural diagonal into the pullback square on extension action categories -/
@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction
open GroupCompletion ActionLocalization

/-- Subtracting the two middle-term coordinates lands in the actual kernel. -/
def extensionDiagonalDifference {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    (extensionProductFiber R p p).of.obj.left ⟶ (extensionKernelIsoObject R p).of :=
  (((exactStructure R).extensionKernelData p.of).isLimit _).lift
    (KernelFork.ofι (pullback.snd _ _ - pullback.fst _ _) (by
      simp only [Preadditive.sub_comp, pullback.condition, sub_self]))

/-- The difference coordinate satisfies the kernel universal property. -/
@[reassoc (attr := simp)]
theorem extensionDiagonalDifference_ι {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    extensionDiagonalDifference R p ≫ ((exactStructure R).extensionKernelData p.of).ι =
      pullback.snd p.of.obj.hom p.of.obj.hom - pullback.fst _ _ :=
  (((exactStructure R).extensionKernelData p.of).isLimit _).fac _ WalkingParallelPair.zero

/-- Add a kernel element to the second coordinate, retaining the first. -/
def extensionDiagonalMiddleHom {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    ((extensionKernelIsoObject R p) ⊙ₗ p).of.obj.left ⟶
      (extensionProductFiber R p p).of.obj.left :=
  pullback.lift (coprod.desc 0 (𝟙 _))
    (coprod.desc ((exactStructure R).extensionKernelData p.of).ι (𝟙 _)) (by
      simp only [coprod.desc_comp, zero_comp, Category.id_comp,
        ((exactStructure R).extensionKernelData p.of).zero])

/-- The difference after adding a kernel element is exactly that element. -/
@[reassoc (attr := simp)]
theorem extensionDiagonalMiddleHom_difference {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    extensionDiagonalMiddleHom R p ≫ extensionDiagonalDifference R p =
      coprod.desc (𝟙 _) 0 := by
  apply Fork.IsLimit.hom_ext (((exactStructure R).extensionKernelData p.of).isLimit _)
  change (extensionDiagonalMiddleHom R p ≫ extensionDiagonalDifference R p) ≫
      ((exactStructure R).extensionKernelData p.of).ι = _
  simp only [Category.assoc, extensionDiagonalDifference_ι, Preadditive.comp_sub,
    extensionDiagonalMiddleHom, pullback.lift_fst, pullback.lift_snd]
  apply coprod.hom_ext <;> simp [Preadditive.comp_sub]

/-- An actual middle-term isomorphism representing the diagonal in the action category. -/
def extensionDiagonalMiddleIso {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    ((extensionKernelIsoObject R p) ⊙ₗ p).of.obj.left ≅
      (extensionProductFiber R p p).of.obj.left where
  hom := extensionDiagonalMiddleHom R p
  inv := extensionDiagonalDifference R p ≫ coprod.inl + pullback.fst _ _ ≫ coprod.inr
  hom_inv_id := by
    simp only [Preadditive.comp_add, extensionDiagonalMiddleHom_difference_assoc]
    apply coprod.hom_ext
    · simp only [coprod.desc_comp, Category.id_comp, zero_comp, extensionDiagonalMiddleHom,
    limit.lift_π_assoc,
        PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app, Preadditive.comp_add,
        colimit.ι_desc, BinaryCofan.mk_pt,
        BinaryCofan.mk_inl, add_zero]
      exact (Category.comp_id _).symm
    · simp only [coprod.desc_comp, Category.id_comp, zero_comp, extensionDiagonalMiddleHom,
    limit.lift_π_assoc,
        PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app, Preadditive.comp_add,
        colimit.ι_desc, BinaryCofan.mk_pt,
        BinaryCofan.mk_inr, zero_add]
      exact (Category.comp_id _).symm
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [extensionDiagonalMiddleHom, Preadditive.add_comp]
    · simp [extensionDiagonalMiddleHom, Preadditive.add_comp, Category.assoc]

/-- The middle-term diagonal decomposition preserves the fixed quotient. -/
def extensionDiagonalIso {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    extensionKernelIsoObject R p ⊙ₗ p ≅ extensionProductFiber R p p :=
  Core.isoMk ((exactStructure R).extensionProperty C |>.isoMk
    (Over.isoMk (extensionDiagonalMiddleIso R p) (by
      change extensionDiagonalMiddleHom R p ≫
        (pullback.snd _ _ ≫ p.of.obj.hom) = coprod.desc 0 p.of.obj.hom
      simp [extensionDiagonalMiddleHom, coprod.desc_comp,
        ((exactStructure R).extensionKernelData p.of).zero])))

/-- The actual diagonal action-category arrow is represented by the original kernel. -/
def extensionActionDiagonal {C : Category.{u, u} R} (p : ExtensionActionCategory R C) :
    p ⟶ ⟨extensionProductFiber R p.obj p.obj⟩ :=
  mkHom ⟨extensionKernelIsoObject R p.obj, (extensionDiagonalIso R p.obj).hom⟩

/-- The diagonal section is the ordinary pullback diagonal on middle objects. -/
@[reassoc (attr := simp)]
theorem extensionActionDiagonal_section_fst {C : Category.{u, u} R}
    (p : ExtensionActionCategory R C) :
    extensionActionSection R (extensionActionDiagonal R p) ≫
      pullback.fst p.obj.of.obj.hom p.obj.of.obj.hom = 𝟙 _ := by
  change (coprod.inr ≫ extensionDiagonalMiddleHom R p.obj) ≫ _ = _
  simp [extensionDiagonalMiddleHom]

/-- The second diagonal coordinate is also the identity. -/
@[reassoc (attr := simp)]
theorem extensionActionDiagonal_section_snd {C : Category.{u, u} R}
    (p : ExtensionActionCategory R C) :
    extensionActionSection R (extensionActionDiagonal R p) ≫
      pullback.snd p.obj.of.obj.hom p.obj.of.obj.hom = 𝟙 _ := by
  change (coprod.inr ≫ extensionDiagonalMiddleHom R p.obj) ≫ _ = _
  simp [extensionDiagonalMiddleHom]

/-- The diagonal's specified retraction is the first pullback projection. -/
@[simp]
theorem extensionActionDiagonal_retraction {C : Category.{u, u} R}
    (p : ExtensionActionCategory R C) :
    extensionActionRetraction R (extensionActionDiagonal R p) =
      pullback.fst p.obj.of.obj.hom p.obj.of.obj.hom := by
  change (extensionDiagonalMiddleIso R p.obj).inv ≫ coprod.desc 0 (𝟙 _) = _
  simp [extensionDiagonalMiddleIso, Preadditive.add_comp]

/-- The genuine diagonal is natural for all action-category arrows, including
changes of kernel by new projective summands. -/
def extensionActionDiagonalNatTrans (C : Category.{u, u} R) :
    𝟭 (ExtensionActionCategory R C) ⟶
      Functor.diag (ExtensionActionCategory R C) ⋙ extensionActionMultiplication R C where
  app p := extensionActionDiagonal R p
  naturality {p q} f := by
    apply extensionAction_hom_ext R
    · simp only [Functor.id_map, Functor.comp_map, Functor.diag_map,
        extensionActionMultiplication, extensionActionSection_comp]
      apply pullback.hom_ext <;> simp [Category.assoc]
    · simp only [Functor.id_map, Functor.comp_map, Functor.diag_map,
        extensionActionMultiplication, extensionActionRetraction_comp]
      erw [extensionActionDiagonal_retraction R q, extensionActionDiagonal_retraction R p]
      exact (extensionProductHom_retraction_fst R f f).symm

end ModuleCat.FiniteProjective
