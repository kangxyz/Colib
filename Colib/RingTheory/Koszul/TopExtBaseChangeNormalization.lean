/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.ScalarExtensionComparison
public import Colib.RingTheory.Koszul.TopExtBaseChangeQuotient
public import Colib.CategoryTheory.Abelian.Projective.CochainComparison
public import Colib.CategoryTheory.Abelian.Projective.ExactFunctor

/-!
# Native top Koszul classes under scalar extension

The actual exterior-power comparison between the Koszul resolutions identifies
scalar extension of a standard top cocycle with the standard top cocycle over
the target ring. This includes the empty sequence and arbitrary coefficients.
The functor is exact and both native resolutions are the existing Stacks ones.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra

universe u w z

namespace Koszul

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Flat scalar extension preserves Koszul regularity in the native complex. -/
theorem isKoszulRegular_algebraMap_of_flat [Module.Flat R A]
    {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f) :
    IsKoszulRegular (fun i => algebraMap R A (f i)) := by
  let F := ModuleCat.extendScalars (algebraMap R A)
  let : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  intro i hi
  have h : IsZero (((F.mapHomologicalComplex (.down ℕ)).obj (seqComplex f)).homology i) :=
    (F.map_isZero (hf i hi)).of_iso ((seqComplex f).sc i |>.mapHomologyIso F)
  exact h.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (seqComplexBaseChangeIso (A := A) f)).symm

/-- The inverse chain comparison identifies the genuine quotient augmentations. -/
theorem seqComplexBaseChangeIso_inv_augmentation {n : ℕ} (f : Fin n → R) :
    (seqComplexBaseChangeIso (A := A) f).inv.f 0 ≫
      (ModuleCat.extendScalars (algebraMap R A)).map ((koszulAugmentation f).f 0) =
    (koszulAugmentation (fun i => algebraMap R A (f i))).f 0 ≫
      (seqQuotientBaseChangeIso (A := A) f).inv := by
  apply (cancel_epi ((seqComplexBaseChangeIso (A := A) f).hom.f 0)).mp
  erw [← Category.assoc, (HomologicalComplex.Hom.isoApp
    (seqComplexBaseChangeIso (A := A) f) 0).hom_inv_id, Category.id_comp]
  erw [← Category.assoc, seqComplexBaseChangeIso_augmentation, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Exact scalar extension sends the literal standard class to the native target standard class.
The source identification is the inverse of the actual tensor/quotient equivalence. -/
theorem seqTopExtClass_mapExactFunctor_normalized
    [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)]
    [PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A))]
    {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f)
    (hfA : IsKoszulRegular (fun i => algebraMap R A (f i)))
    (N : ModuleCat.{u} R) (m : N) :
    (Ext.mk₀ (seqQuotientBaseChangeIso (A := A) f).inv).comp
      ((seqTopExtClass f hf N m).mapExactFunctor
        (ModuleCat.extendScalars (algebraMap R A))) (zero_add n) =
      seqTopExtClass (fun i => algebraMap R A (f i)) hfA
        ((ModuleCat.extendScalars (algebraMap R A)).obj N)
        ((1 : A) ⊗ₜ[R, algebraMap R A] m) := by
  let F := ModuleCat.extendScalars (algebraMap R A)
  let P := seqProjectiveResolution f hf
  let Q := seqProjectiveResolution (fun i => algebraMap R A (f i)) hfA
  let h := (seqComplexBaseChangeIso (A := A) f).inv
  let φ := ProjectiveResolution.cochainComparison F P Q h
  rw [seqTopExtClass_apply, seqTopExtClass_apply]
  apply ProjectiveResolution.ExactFunctor.mk₀_comp_extMk_mapExactFunctor
    F P Q (seqQuotientBaseChangeIso (A := A) f).inv φ
  · exact ProjectiveResolution.cochainComparison_comp_π' F P Q h _
      (seqComplexBaseChangeIso_inv_augmentation f)
  · apply ProjectiveResolution.cochainComparison_component F P Q h
    apply (cancel_epi ((seqComplexBaseChangeIso (A := A) f).hom.f n)).mp
    simp only [← Category.assoc]
    erw [(HomologicalComplex.Hom.isoApp
      (seqComplexBaseChangeIso (A := A) f) n).hom_inv_id, Category.id_comp]
    simpa only [Category.assoc] using seqComplexBaseChangeIso_topCocycle (A := A) f N m

/-- For a flat algebra, regularity of the native target sequence and exactness are automatic. -/
theorem seqTopExtClass_baseChange_of_flat
    [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)] [Module.Flat R A]
    {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) (m : N) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _ (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (Ext.mk₀ (seqQuotientBaseChangeIso (A := A) f).inv).comp
      ((seqTopExtClass f hf N m).mapExactFunctor
        (ModuleCat.extendScalars (algebraMap R A))) (zero_add n) =
      seqTopExtClass (fun i => algebraMap R A (f i))
        (isKoszulRegular_algebraMap_of_flat f hf)
        ((ModuleCat.extendScalars (algebraMap R A)).obj N)
        ((1 : A) ⊗ₜ[R, algebraMap R A] m) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
    extendScalars_preservesFiniteLimits_of_flat' _ (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact seqTopExtClass_mapExactFunctor_normalized f hf _ N m

/-- Localization on top Ext with the literal native sequence quotient as its source. -/
theorem seqTopExtScalarExtension_native_isLocalizedModule
    [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)]
    (T : Submonoid R) [IsLocalization T A]
    {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    IsLocalizedModule T
      (((Ext.mk₀ (seqQuotientBaseChangeIso (A := A) f).inv).precompOfLinear R
          ((ModuleCat.extendScalars (algebraMap R A)).obj N) (zero_add n)).comp
        ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
          (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n)) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
    extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
  let : IsLocalizedModule T
      ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n) :=
    seqTopExtScalarExtension_isLocalizedModule T f hf N
  exact IsLocalizedModule.of_linearEquiv T _
    (LinearEquiv.ofBijective
      ((Ext.mk₀ (seqQuotientBaseChangeIso (A := A) f).inv).precompOfLinear R
        ((ModuleCat.extendScalars (algebraMap R A)).obj N) (zero_add n))
      (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ n))

end Koszul

attribute [colib_tag "COL-0167",
  colib_ref "axiom_stacks" "RingTheory/Koszul/FlatBaseChange.lean" "adaptation"
    "Ingredient: actual exterior-power scalar extension and differential compatibility"]
  Koszul.seqTopExtClass_mapExactFunctor_normalized
  Koszul.seqTopExtClass_baseChange_of_flat
  Koszul.seqTopExtScalarExtension_native_isLocalizedModule
