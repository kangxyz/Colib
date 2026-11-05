/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.TopExtAllLengths
public import Colib.Util.References

/-!
# Naturality and scalar actions for all-length top Ext coefficients

The unified coefficient quotient equivalence commutes with actual coefficient
quotient maps and Yoneda postcomposition in every length, including the empty
sequence. Its quotient-ring action is actual source multiplication, and ring
representatives also act by scalar multiplication on the target coefficient.

This completes the all-length canonical-model naturality of
`ChainComplex.Koszul.topExtQuotientLinearEquiv_naturality` from
`Aglib.Algebra.Homology.Koszul.Ext.Coefficients` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Positive-length naturality and the
generic native Ext scalar identities are reused, without another quotient action.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f)

/-- The all-length quotient equivalence intertwines actual coefficient maps and Yoneda maps. -/
theorem seqTopExtQuotientLinearEquivAll_naturality {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') (x : N ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R N))) :
    (seqTopExtQuotientLinearEquivAll f hf N x).comp (Ext.mk₀ g) (add_zero n) =
      seqTopExtQuotientLinearEquivAll f hf N'
        (((Ideal.span (Set.range f) • (⊤ : Submodule R N)).mapQ
          (Ideal.span (Set.range f) • (⊤ : Submodule R N')) g.hom
          (Submodule.smul_top_le_comap_smul_top (Ideal.span (Set.range f)) g.hom)) x) := by
  cases n with
  | zero =>
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
      (Ideal.span (Set.range f) • (⊤ : Submodule R N)) x
    change (seqTopExtQuotientLinearEquivAll f hf N (Submodule.Quotient.mk m)).comp
        (Ext.mk₀ g) (add_zero 0) =
      seqTopExtQuotientLinearEquivAll f hf N' (Submodule.Quotient.mk (g m))
    rw [seqTopExtQuotientLinearEquivAll_apply_mk, seqTopExtQuotientLinearEquivAll_apply_mk]
    exact seqTopExtClass_comp_mk₀ f hf g m
  | succ n => exact seqTopExtQuotientLinearEquiv_naturality f hf g x

/-- Quotient scalars act by precomposition with multiplication on the actual source quotient. -/
theorem seqTopExtQuotientLinearEquivAll_smul (N : ModuleCat.{u} R)
    (b : R ⧸ Ideal.span (Set.range f))
    (x : N ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R N))) :
    seqTopExtQuotientLinearEquivAll f hf N (b • x) =
      (Ext.mk₀ (Ext.quotientSourceMul (Ideal.span (Set.range f)) b)).comp
        (seqTopExtQuotientLinearEquivAll f hf N x) (zero_add n) := by
  let := Ext.quotientSourceModule (Ideal.span (Set.range f)) N n
  rw [(seqTopExtQuotientLinearEquivAll f hf N).map_smul]
  exact Ext.quotientSourceModule_smul_eq_precomp _ _ _ _ _

/-- A ring representative acts equally by scalar Yoneda postcomposition on coefficients. -/
theorem seqTopExtQuotientLinearEquivAll_mk_smul (N : ModuleCat.{u} R) (r : R)
    (x : N ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R N))) :
    seqTopExtQuotientLinearEquivAll f hf N
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) r • x) =
      (seqTopExtQuotientLinearEquivAll f hf N x).comp (Ext.mk₀ (r • 𝟙 N)) (add_zero n) := by
  let := Ext.quotientSourceModule (Ideal.span (Set.range f)) N n
  rw [(seqTopExtQuotientLinearEquivAll f hf N).map_smul,
    Ext.quotientSourceModule_mk_smul]
  exact Ext.smul_eq_comp_mk₀ _ _

end Koszul

attribute [colib_tag "COL-0138"] Koszul.seqTopExtQuotientLinearEquivAll_naturality
  Koszul.seqTopExtQuotientLinearEquivAll_smul Koszul.seqTopExtQuotientLinearEquivAll_mk_smul

attribute [stacks 06XP "Ingredient: Yoneda composition; quotient scalar identities proved here"]
  Koszul.seqTopExtQuotientLinearEquivAll_smul
