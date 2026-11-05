/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.TopExtLocalization
public import Colib.Algebra.Category.ModuleCat.ChangeOfRings.Linear
public import Colib.Algebra.Category.ModuleCat.ChangeOfRings.Localization
public import Colib.CategoryTheory.Abelian.ExtAdjunctionLinear
public import StacksFrontier.Homology.ExtendScalars.Flat
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Localization of the base ring on native top Ext

The actual exact scalar-extension functor localizes top Ext of a Koszul-regular quotient,
including the empty sequence and arbitrary coefficients. The target is Ext over the localized
ring, with source the actual scalar extension of the quotient. Identifying that source with
the quotient of the localized ring and comparing top generators there are separate results.

This adapts `ChainComplex.Koszul.topExtScalarExtension_isLocalizedModule` from
`Aglib.Algebra.Homology.Koszul.Ext.BaseChange`, replacing its newer Mathlib adjunction API by
Stacks' existing exact-adjunction map and bijectivity. No second resolution is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u w z

namespace Koszul

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)]

/-- Extension to a localization of the base ring localizes native top Ext in every length. -/
theorem seqTopExtScalarExtension_isLocalizedModule (T : Submonoid R) [IsLocalization T A]
    {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    IsLocalizedModule T
      ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
    extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
  let F := ModuleCat.extendScalars (algebraMap R A)
  let adj := ModuleCat.extendRestrictScalarsAdj.{u} (algebraMap R A)
  let X := ModuleCat.of R (R ⧸ Ideal.span (Set.range f))
  let η := adj.unit.app N
  let : IsLocalizedModule T η.hom :=
    ModuleCat.extendRestrictScalarsAdj_unit_isLocalizedModule T (algebraMap R A)
      (by rw [toAlgebra_algebraMap]; infer_instance) N
  let e := Stacks.ExtAdjunction.extMapLinearEquiv adj R X (F.obj N) n
  let q := (Ext.mk₀ η).postcompOfLinear R X (add_zero n)
  let : IsLocalizedModule T q := seqTopExtPostcomp_isLocalizedModule T η f hf
  have he : F.mapExtLinearMap R X N n = e.toLinearMap.comp q :=
    (Stacks.ExtAdjunction.extMapLinear_comp_unit adj R X N n).symm
  change IsLocalizedModule T (F.mapExtLinearMap R X N n)
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T q e

end Koszul

attribute [colib_tag "COL-0165",
  colib_ref "axiom_stacks" "Homology/ExtendScalars/Flat.lean" "adaptation"
    "Ingredient: exact native scalar extension for flat algebras"]
  Koszul.seqTopExtScalarExtension_isLocalizedModule
