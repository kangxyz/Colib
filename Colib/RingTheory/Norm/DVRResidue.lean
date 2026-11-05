/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Norm.FiniteAlgebra
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.RingTheory.Norm.BaseChangeProduct

/-!
# Integral norms on DVR residue fields and residue units

The literal closed fibre is `S / (maximalIdeal R)S`. Norm base change and the
finite-local-algebra norm formula give the residue norm with exponent equal to the
self-length of this fibre. Its residue field is identified with `ResidueField S`
through the native map induced by the actual quotient map.

For DVRs, an equation `algebraMap R S π = u * ϖ^e` between irreducible uniformizers
proves `(maximalIdeal R)S = (maximalIdeal S)^e`, and then proves that the fibre has
self-length `e`. This is not an assumed length or ramification-index equality.
Finite generation and torsion-freeness supply the free module needed to compare the
actual `Algebra.intNorm` with the determinant norm. The final formulas retain the
original two residue maps, also on their native unit groups.

No completeness, separability, reduced-fibre, or residue-characteristic hypothesis
is used. The generic finite-free local-algebra result does not require either ring
to be a DVR or Noetherian. The independent ideal and length calculations do not
require finiteness, torsion-freeness, or a local algebra map.

## Source provenance

Adapted from `Aglib/RingTheory/DVRNormResidueUnit.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`9f06fc047a51a8d312fb8e48aa26babbb023c8db4b8b0e964f2cd2776c1bdab5`.
The original module is `Motivic.Aglib.RingTheory.DVRNormResidueUnit`, with source
SHA-256 `642b092482d3dbba6fad1c43554de5885caff56a037f26c76c5ede3a6817822f`,
as recorded in Aglib's `docs/migration/motivic-milnor-k.json`.

Norm base change directly reuses `Stacks.Norm.norm_tmul_one`. The local norm formula
reuses the delivered `Algebra.norm_eq_quotient_norm_pow_length`; no alternate norm,
fibre, residue field, or filtration model is introduced.

## References

* Stacks 0BD2: determinant norm and its compatibility with base change, specialized
  here to the closed fibre of a finite free affine algebra, also allowing rank zero.
* Stacks 0GSZ: the finite-length scalar determinant formula used on the closed fibre.
* Stacks 09E4: the characterization of the ramification exponent by uniformizers and
  extended maximal ideals. Existence and independence of uniformizer choices are
  not claimed by the two standalone ideal-and-length lemmas.

This is an algebraic residue-norm calculation, not a norm-residue-symbol, Milnor-transfer,
or motivic compatibility theorem.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing R]
  [Algebra R S] [Module.Free R S] [Module.Finite R S]

/-- The determinant norm specializes to the literal closed fibre. -/
@[stacks 0BD2 "affine closed-fibre norm base change, also allowing rank zero",
  colib_tag "COL-0193"]
theorem norm_closedFiber (b : S) :
    let _ : Algebra (ResidueField R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    Algebra.norm (ResidueField R)
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b) =
        residue R (Algebra.norm R b) := by
  let : Algebra (ResidueField R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let ε := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R)
  have h := Algebra.norm_eq_of_algEquiv ε
    (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b)
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Stacks.Norm.norm_tmul_one] at h
  exact h.symm

variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- Reduction of a finite-free local algebra norm keeps the full self-length of
the actual closed fibre, including its nilpotents and inseparable residue fields. -/
@[stacks 0GSZ "closed-fibre scalar determinant, after norm base change",
  colib_tag "COL-0193"]
theorem residue_norm_eq_norm_residue_pow_length (b : S) :
    residue R (Algebra.norm R b) =
      Algebra.norm (ResidueField R) (residue S b) ^
        (Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
          (S ⧸ (maximalIdeal R).map (algebraMap R S))).toNat := by
  let I := (maximalIdeal R).map (algebraMap R S)
  let B := S ⧸ I
  let : Algebra (ResidueField R) B :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R (ResidueField R) B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hI : I ≠ ⊤ := ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S))
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing B := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap R B) := by
    change IsLocalHom ((Ideal.Quotient.mk I).comp (algebraMap R S))
    infer_instance
  let : IsLocalHom (IsScalarTower.toAlgHom R S B) :=
    ⟨fun b hb => IsUnit.of_map (Ideal.Quotient.mk I) b hb⟩
  let : Module.Finite (ResidueField R) B := Module.Finite.of_restrictScalars_finite R _ _
  let φ : ResidueField S →ₐ[ResidueField R] ResidueField B :=
    ResidueField.mapAlgHom' (IsScalarTower.toAlgHom R S B)
  have hφ (s : S) : φ (residue S s) = residue B (Ideal.Quotient.mk I s) :=
    ResidueField.mapAlgHom'_residue (IsScalarTower.toAlgHom R S B) s
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨b, rfl⟩ := residue_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨residue S s, hφ s⟩
  let ε : ResidueField S ≃ₐ[ResidueField R] ResidueField B :=
    AlgEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have hn : Algebra.norm (ResidueField R) (residue B (Ideal.Quotient.mk I b)) =
      Algebra.norm (ResidueField R) (residue S b) := by
    rw [← hφ]
    exact Algebra.norm_eq_of_algEquiv ε (residue S b)
  let δ : (B ⧸ maximalIdeal B) ≃ₐ[ResidueField R] ResidueField B :=
    { RingEquiv.refl (B ⧸ maximalIdeal B) with
      commutes' x := by
        obtain ⟨r, rfl⟩ := residue_surjective x
        rfl }
  calc
    _ = Algebra.norm (ResidueField R) (Ideal.Quotient.mk I b) :=
      (norm_closedFiber R S b).symm
    _ = Algebra.norm (ResidueField R) (residue B (Ideal.Quotient.mk I b)) ^
        (Module.length B B).toNat := by
      have h := Algebra.norm_eq_quotient_norm_pow_length (k := ResidueField R) (B := B)
        (Ideal.Quotient.mk I b)
      rw [← Algebra.norm_eq_of_algEquiv δ] at h
      exact h
    _ = _ := congrArg (fun x => x ^ (Module.length B B).toNat) hn

end Algebra

namespace IsDiscreteValuationRing

variable (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]

/-- The given uniformizer equation identifies the extended maximal ideal.
This standalone ideal identity does not assume the map is finite or local. -/
@[stacks 09E4 "uniformizer equation implies extended-maximal-ideal equation",
  colib_tag "COL-0194"]
theorem map_maximalIdeal_eq_pow_of_uniformizer
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ e := by
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, he,
    Ideal.span_singleton_mul_left_unit u.isUnit, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

/-- The literal closed-fibre self-length equals the given uniformizer exponent.
The equality is in extended naturals before applying `ENat.toNat`. -/
@[colib_tag "COL-0194"]
theorem closedFiber_length_eq_ramification
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (S ⧸ (maximalIdeal R).map (algebraMap R S)) = e := by
  rw [← Module.length_eq_of_surjective (S := S) Ideal.Quotient.mk_surjective,
    map_maximalIdeal_eq_pow_of_uniformizer R S hπ hϖ u e he]
  exact length_quotient_pow_maximalIdeal S e

end IsDiscreteValuationRing

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]

/-- The actual integral norm reduces to the residue-field norm raised to the
proved uniformizer exponent, for every element and in arbitrary characteristic. -/
@[colib_tag "COL-0194",
  colib_ref "aglib_principal_euler_pin" "RingTheory/DVRNormResidueUnit.lean"
    "adaptation" "Actual integral and residue-unit norms with proved closed-fibre exponent"]
theorem residue_intNorm_eq_norm_residue_pow
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    residue R (Algebra.intNorm R S b) =
      Algebra.norm (ResidueField R) (residue S b) ^ e := by
  let : Module.Free R S := Module.free_of_finite_type_torsion_free'
  rw [Algebra.intNorm_eq_norm, residue_norm_eq_norm_residue_pow_length,
    IsDiscreteValuationRing.closedFiber_length_eq_ramification R S hπ hϖ u e he,
    ENat.toNat_natCast]

/-- The unit-valued residue norm formula uses the original integral norm and
the original two residue maps. No separability of the residue extension is assumed. -/
@[colib_tag "COL-0194"]
theorem residueUnits_intNorm_eq_norm_pow
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : Sˣ) :
    Units.map (residue R).toMonoidHom (Units.map (Algebra.intNorm R S) b) =
      Units.map (Algebra.norm (ResidueField R))
        (Units.map (residue S).toMonoidHom b) ^ e := by
  apply Units.ext
  exact residue_intNorm_eq_norm_residue_pow R S hπ hϖ u e he (b : S)

end Algebra
