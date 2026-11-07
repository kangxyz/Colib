/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.SmallModel.Abelian
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Actual localizations on the native small model

An exact localization descends through Mathlib's chosen small-model equivalences.
The descended functor is literally `ExactFunctor.smallModel.toFunctor`, and
the class of supported objects is its actual kernel. No replacement quotient
functor or separate model is introduced.

## Implementation provenance

The localization transport argument is generalized from
`Quillen/Aglib/Algebra/Category/FGModuleCat/SmallModelLocalization.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original categorical
localization predicate and the canonical unit comparison are retained, with
independent source, target and smallness universes.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.ExactCategory.ExactFunctor

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))

instance smallModel_preservesFiniteLimits [PreservesFiniteLimits F.toFunctor] :
    PreservesFiniteLimits F.smallModel.toFunctor := by
  change PreservesFiniteLimits (((equivSmallModel C).inverse ⋙ F.toFunctor) ⋙
    (equivSmallModel D).functor)
  have := comp_preservesFiniteLimits (equivSmallModel C).inverse F.toFunctor
  exact comp_preservesFiniteLimits _ _

instance smallModel_preservesFiniteColimits [PreservesFiniteColimits F.toFunctor] :
    PreservesFiniteColimits F.smallModel.toFunctor := by
  change PreservesFiniteColimits (((equivSmallModel C).inverse ⋙ F.toFunctor) ⋙
    (equivSmallModel D).functor)
  have := comp_preservesFiniteColimits (equivSmallModel C).inverse F.toFunctor
  exact comp_preservesFiniteColimits _ _

/-- The source equivalence commutes with the descended functor by its
canonical unit isomorphism. -/
def smallModelComparison :
    (equivSmallModel C).functor ⋙ F.smallModel.toFunctor ≅
      F.toFunctor ⋙ (equivSmallModel D).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (equivSmallModel C).unitIso.symm _ ≪≫
      Functor.leftUnitor _) _

/-- The kernel of the descended functor consists exactly of the objects
represented by objects in the original kernel. -/
theorem smallModel_kernel_iff (M : SmallModel.{w} C) :
    F.smallModel.toFunctor.kernel M ↔
      F.toFunctor.kernel ((equivSmallModel C).inverse.obj M) := by
  change IsZero ((equivSmallModel D).functor.obj
      (F.toFunctor.obj ((equivSmallModel C).inverse.obj M))) ↔
    IsZero (F.toFunctor.obj ((equivSmallModel C).inverse.obj M))
  exact ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero _ _ h,
    fun h ↦ Functor.map_isZero _ h⟩

variable [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]

/-- The descended exact functor remains a localization at the Serre
isomorphisms of its own actual kernel. -/
instance smallModel_isLocalization
    [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre] :
    F.smallModel.toFunctor.IsLocalization F.smallModel.toFunctor.kernel.isoModSerre := by
  let L := F.toFunctor ⋙ (equivSmallModel D).functor
  have hinv : F.smallModel.toFunctor.kernel.isoModSerre.IsInvertedBy
      F.smallModel.toFunctor := by
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro X Y f hf
    exact hf
  apply Functor.IsLocalization.of_equivalence_source L F.toFunctor.kernel.isoModSerre
    F.smallModel.toFunctor F.smallModel.toFunctor.kernel.isoModSerre
    (equivSmallModel C) ?_ hinv (F.smallModelComparison)
  have hi : F.toFunctor.kernel.isoModSerre.IsInvertedBy
      ((equivSmallModel C).functor ⋙ F.smallModel.toFunctor) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ F.smallModelComparison).2
      (Localization.inverts L F.toFunctor.kernel.isoModSerre)
  intro M N f hf
  apply MorphismProperty.le_isoClosure
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

end CategoryTheory.ExactCategory.ExactFunctor
