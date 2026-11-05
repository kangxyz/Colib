/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.TopExtAllLengths
public import Colib.Util.References
public import Colib.Algebra.Module.LocalizedModule.IdealQuotient

/-!
# Coefficient localization of native top Koszul Ext in every length

Yoneda postcomposition by an actual coefficient module localization map is a
localization on top Ext of a Koszul-regular quotient. The base ring and quotient
source stay fixed; coefficients require no flatness, finiteness or regularity.
Empty sequences are included through the same existing top-coordinate class.

Adapted from `ChainComplex.Koszul.topExtPostcomp_isLocalizedModule` in
`Aglib.Algebra.Homology.Koszul.Ext.Localization` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Base-ring localization and a comparison
with the old named cocycle are separate statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] (T : Submonoid R)
  {N N' : ModuleCat.{u} R} (g : N ⟶ N') [IsLocalizedModule T g.hom]
  [HasExt.{w} (ModuleCat.{u} R)] {n : ℕ}

/-- Native Yoneda postcomposition by an actual coefficient localization map
localizes the top Ext of a Koszul-regular quotient. -/
theorem seqTopExtPostcomp_isLocalizedModule (f : Fin n → R)
    (hf : IsKoszulRegular f) :
    IsLocalizedModule T
      ((Ext.mk₀ g).postcompOfLinear R (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))
        (add_zero n)) := by
  let e := seqTopExtLinearEquivAll.{u,w} f hf N
  let e' := seqTopExtLinearEquivAll.{u,w} f hf N'
  let q := ((Ideal.span (Set.range f)) • (⊤ : Submodule R N)).mapQ
    ((Ideal.span (Set.range f)) • (⊤ : Submodule R N')) g.hom
      (Submodule.smul_top_le_comap_smul_top (Ideal.span (Set.range f)) g.hom)
  let : IsLocalizedModule T q :=
    Submodule.isLocalizedModule_mapQ_smul_top T g.hom (Ideal.span (Set.range f))
  let : IsLocalizedModule T (q.comp e.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right T q e.symm
  have hloc : IsLocalizedModule T (e'.toLinearMap.comp (q.comp e.symm.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv T (q.comp e.symm.toLinearMap) e'
  have heq : (Ext.mk₀ g).postcompOfLinear R (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))
        (add_zero n) = e'.toLinearMap.comp (q.comp e.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := seqTopExtClass_surjective f hf N x
    have he : e.symm (seqTopExtClass f hf N m) = Submodule.Quotient.mk m := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      exact (seqTopExtLinearEquivAll_apply_mk f hf N m).symm
    change (seqTopExtClass f hf N m).comp (Ext.mk₀ g) (add_zero n) =
      e' (q (e.symm (seqTopExtClass f hf N m)))
    rw [he]
    have hq : q (Submodule.Quotient.mk m) = Submodule.Quotient.mk (g m) := rfl
    rw [hq, seqTopExtClass_comp_mk₀]
    exact (seqTopExtLinearEquivAll_apply_mk f hf N' (g m)).symm
  rw [heq]
  exact hloc

end Koszul

attribute [colib_tag "COL-0142"] Koszul.seqTopExtPostcomp_isLocalizedModule
attribute [stacks 06XP "Ingredient: Yoneda composition; coefficient localization proved here"]
  Koszul.seqTopExtPostcomp_isLocalizedModule
