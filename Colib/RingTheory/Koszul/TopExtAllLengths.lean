/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.Projective.ExtZero
public import Colib.RingTheory.Koszul.TopExtCoefficients
public import Colib.Util.References

/-!
# Top Koszul Ext coefficients including the empty sequence

The existing top-coordinate cocycle is injective for an empty sequence, since
degree-zero resolution cocycles have no boundaries. Together with the existing
positive-length calculation this gives one quotient-linear coefficient formula
in every length. Positive-length proofs and models are reused unchanged.

This completes the empty-list scope of the coefficient quotient endpoints in
`Aglib.Algebra.Homology.Koszul.Ext.Coefficients` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, in the chosen Stacks model.
It does not identify the old named cocycle, and
does not supply an all-length naturality or additive-equivalence comparison API.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

/-- Empty-sequence top classes vanish only at the zero coefficient. -/
theorem seqTopExtClass_empty_eq_zero_iff (f : Fin 0 → R) (hf : IsKoszulRegular f)
    (N : ModuleCat.{u} R) (x : N) : seqTopExtClass f hf N x = 0 ↔ x = 0 := by
  rw [seqTopExtClass_apply]
  erw [ProjectiveResolution.extMk_zero_eq_zero_iff]
  constructor
  · intro h
    have hz := ConcreteCategory.congr_hom h (topGen R 0)
    change topEquiv R 0 (topGen R 0) • x = 0 at hz
    simpa using hz
  · intro hx
    subst x
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact smul_zero _

/-- In every length, including zero, the exact top-class kernel is the ideal times N. -/
theorem seqTopExtClass_ker_all {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f)
    (N : ModuleCat.{u} R) :
    LinearMap.ker (seqTopExtClass f hf N) = Ideal.span (Set.range f) • (⊤ : Submodule R N) := by
  cases n with
  | zero =>
    ext x
    change seqTopExtClass f hf N x = 0 ↔ _
    rw [seqTopExtClass_empty_eq_zero_iff]
    simp
  | succ n => exact seqTopExtClass_ker f hf N

/-- In every length, the actual coefficient quotient maps to the standard top cocycle. -/
def seqTopExtLinearEquivAll {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f)
    (N : ModuleCat.{u} R) :
    (N ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R N))) ≃ₗ[R]
      Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n :=
  (Submodule.quotEquivOfEq _ _ (seqTopExtClass_ker_all f hf N).symm).trans
    ((seqTopExtClass f hf N).quotKerEquivOfSurjective (seqTopExtClass_surjective f hf N))

/-- The all-length equivalence keeps the existing literal top-coordinate representative. -/
@[simp]
theorem seqTopExtLinearEquivAll_apply_mk {n : ℕ} (f : Fin n → R)
    (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) (x : N) :
    seqTopExtLinearEquivAll f hf N (Submodule.Quotient.mk x) = seqTopExtClass f hf N x := by
  simp only [seqTopExtLinearEquivAll, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The native coefficient quotient formula is quotient-linear in every sequence length. -/
def seqTopExtQuotientLinearEquivAll {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f)
    (N : ModuleCat.{u} R) :
    letI := Ext.quotientSourceModule (Ideal.span (Set.range f)) N n
    (N ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R N))) ≃ₗ[R ⧸ Ideal.span (Set.range f)]
      Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n := by
  cases n with
  | zero =>
    letI := Ext.quotientSourceModule (Ideal.span (Set.range f)) N 0
    refine { __ := (seqTopExtLinearEquivAll f hf N).toAddEquiv, map_smul' := ?_ }
    intro b x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
      (Ideal.span (Set.range f) • (⊤ : Submodule R N)) x
    change seqTopExtLinearEquivAll f hf N
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) r • Submodule.Quotient.mk m) =
      Ideal.Quotient.mk (Ideal.span (Set.range f)) r •
        seqTopExtLinearEquivAll f hf N (Submodule.Quotient.mk m)
    rw [Module.Quotient.mk_smul_mk, seqTopExtLinearEquivAll_apply_mk,
      seqTopExtLinearEquivAll_apply_mk, Ext.quotientSourceModule_mk_smul]
    exact (seqTopExtClass f hf N).map_smul r m
  | succ n => exact seqTopExtQuotientLinearEquiv f hf N

/-- Every quotient representative retains its existing class, also for the empty sequence. -/
@[simp]
theorem seqTopExtQuotientLinearEquivAll_apply_mk {n : ℕ} (f : Fin n → R)
    (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) (x : N) :
    seqTopExtQuotientLinearEquivAll f hf N (Submodule.Quotient.mk x) =
      seqTopExtClass f hf N x := by
  cases n with
  | zero => exact seqTopExtLinearEquivAll_apply_mk f hf N x
  | succ n => exact seqTopExtQuotientLinearEquiv_apply_mk f hf N x

/-- At positive length, the unified quotient equivalence is exactly the existing one. -/
theorem seqTopExtQuotientLinearEquivAll_succ {n : ℕ} (f : Fin (n + 1) → R)
    (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) :
    seqTopExtQuotientLinearEquivAll f hf N = seqTopExtQuotientLinearEquiv f hf N := rfl

end Koszul

attribute [colib_tag "COL-0137"] Koszul.seqTopExtClass_empty_eq_zero_iff
  Koszul.seqTopExtClass_ker_all Koszul.seqTopExtLinearEquivAll
  Koszul.seqTopExtQuotientLinearEquivAll Koszul.seqTopExtQuotientLinearEquivAll_succ

attribute [stacks 06XP "Ext background only; empty-sequence quotient proved here"]
  Koszul.seqTopExtQuotientLinearEquivAll
