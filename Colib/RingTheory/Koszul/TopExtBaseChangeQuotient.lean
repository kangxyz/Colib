/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.TopExtBaseChange
public import Colib.Algebra.Category.ModuleCat.ChangeOfRings.Quotient

/-!
# Base change of top Ext with its actual quotient source

Scalar extension followed by the canonical quotient-source comparison is a localization map
into `Ext_A(A / IA, A ⊗ N)`. The source comparison is the native tensor/quotient equivalence.
This does not yet identify the transported cocycle with the native top cocycle over `A`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u w z

namespace Koszul

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)]

/-- The native quotient-source comparison induces an equivalence on actual target Ext. -/
def scalarExtensionQuotientExtEquiv (I : Ideal R) (N : ModuleCat.{u} R) (n : ℕ) :
    Ext.{z} ((ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R (R ⧸ I)))
      ((ModuleCat.extendScalars (algebraMap R A)).obj N) n ≃ₗ[R]
    Ext.{z} (ModuleCat.of A (A ⧸ I.map (algebraMap R A)))
      ((ModuleCat.extendScalars (algebraMap R A)).obj N) n :=
  LinearEquiv.ofBijective
    ((Ext.mk₀ (ModuleCat.extendScalarsQuotientIso (A := A) I).inv).precompOfLinear R
      ((ModuleCat.extendScalars (algebraMap R A)).obj N) (zero_add n))
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ n)

/-- Scalar extension with the literal quotient source is a localization on top Ext. -/
theorem seqTopExtScalarExtensionQuotient_isLocalizedModule
    (T : Submonoid R) [IsLocalization T A]
    {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    IsLocalizedModule T
      ((scalarExtensionQuotientExtEquiv (A := A) (Ideal.span (Set.range f)) N n).toLinearMap.comp
        ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
          (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n)) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
    extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
  let : IsLocalizedModule T
      ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n) :=
    seqTopExtScalarExtension_isLocalizedModule T f hf N
  exact IsLocalizedModule.of_linearEquiv T _ _

/-- The scalar-extended standard class has its literal coefficient under the exact adjunction.
This is a normalization in the original Koszul complex with restricted coefficients, not a
claim about the top-coordinate cocycle of the new Koszul complex over `A`. -/
theorem seqTopExtClass_mapExactFunctor_eq_extMap
    (T : Submonoid R) [IsLocalization T A]
    {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) (m : N) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    (seqTopExtClass f hf N m).mapExactFunctor (ModuleCat.extendScalars (algebraMap R A)) =
      Stacks.ExtAdjunction.extMap (ModuleCat.extendRestrictScalarsAdj (algebraMap R A))
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))
        ((ModuleCat.extendScalars (algebraMap R A)).obj N) n
        (seqTopExtClass f hf _
          ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).unit.app N m)) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
    extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R A)
  have h := LinearMap.congr_fun (Stacks.ExtAdjunction.extMapLinear_comp_unit adj R
    (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n) (seqTopExtClass f hf N m)
  change Stacks.ExtAdjunction.extMap adj _ _ n
    ((seqTopExtClass f hf N m).comp (Ext.mk₀ (adj.unit.app N)) (add_zero n)) = _ at h
  rw [seqTopExtClass_comp_mk₀] at h
  exact h.symm

end Koszul

attribute [colib_tag "COL-0166",
  colib_ref "mathlib_koszul_pin"
    "RingTheory/TensorProduct/Quotient.lean; quotIdealMapEquivTensorQuot"
    "background" "Ingredient: the actual tensor quotient isomorphism and pure-tensor formula"]
  Koszul.scalarExtensionQuotientExtEquiv
  Koszul.seqTopExtScalarExtensionQuotient_isLocalizedModule
