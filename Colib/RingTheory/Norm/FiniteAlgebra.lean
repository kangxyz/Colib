/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Determinant.FiniteLength
public import Colib.RingTheory.Length.FiniteAlgebraLocal
public import Colib.Util.References
public import Mathlib.RingTheory.Norm.Basic

/-!
# Finite-algebra norms and local module lengths

For a finite-dimensional module over a finite algebra over a field, the determinant
of multiplication is the product of the residue-field norms, weighted by the actual
local module lengths. Taking the module to be the algebra gives the norm formula,
including nonreduced algebras and inseparable residue fields.

The proof uses the native semilocal module decomposition and the existing determinant
of finite-length endomorphisms. The actual localized module is compared with its
tensor presentation by `LocalizedModule.equivTensorProduct`; no prime-filtration or
localization model is recreated. The ring and module universes remain independent.

## Source provenance

This adapts `Aglib/RingTheory/FiniteAlgebraNormLength.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`f7f2ad2d3b448b8702d855fb1cd40d744aeecafdb311603f23dde9a484d22899`.
Its original module is `Motivic.Aglib.RingTheory.FiniteAlgebraNormLength`, recorded in
Aglib's `docs/migration/motivic-milnor-k.json`.

Native Stacks revision: `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.
The determinant exact-sequence law is Stacks 0GSY, and the local scalar determinant
formula is Stacks 0GSZ. These lie in Section 0GSX. The ordinary norm is Mathlib's
existing determinant norm.

-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct

namespace Algebra

universe u v

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B]

omit [Module.Finite k B] in
/-- The norm on the actual maximal quotient agrees, through the canonical residue map
of the base field, with the norm on the residue field of the actual localization. -/
theorem residue_norm_quotient_eq_norm_residue (q : MaximalSpectrum B) (b : B)
    [IsLocalHom (algebraMap k (Localization.AtPrime q.asIdeal))] :
    IsLocalRing.residue k (Algebra.norm k (Ideal.Quotient.mk q.asIdeal b)) =
      Algebra.norm (IsLocalRing.ResidueField k)
        (IsLocalRing.residue (Localization.AtPrime q.asIdeal)
          (algebraMap B (Localization.AtPrime q.asIdeal) b)) := by
  let L := Localization.AtPrime q.asIdeal
  let e : k ≃+* IsLocalRing.ResidueField k :=
    RingEquiv.ofBijective (IsLocalRing.residue k)
      ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩
  let E := (Module.finiteAlgebraResidueQuotientEquiv (S := B) q).restrictScalars k
  have hE : E (Ideal.Quotient.mk q.asIdeal b) =
      IsLocalRing.residue L (algebraMap B L b) := by
    change algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField
      (Ideal.Quotient.mk q.asIdeal b) = _
    calc
      _ = algebraMap B q.asIdeal.ResidueField b :=
        Ideal.algebraMap_quotient_residueField_mk q.asIdeal b
      _ = algebraMap L q.asIdeal.ResidueField (algebraMap B L b) :=
        IsScalarTower.algebraMap_apply B L q.asIdeal.ResidueField b
      _ = _ := rfl
  have he : (algebraMap (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField L)).comp e =
      algebraMap k (IsLocalRing.ResidueField L) := by
    ext c
    exact (IsScalarTower.algebraMap_apply k (IsLocalRing.ResidueField k)
      (IsLocalRing.ResidueField L) c).symm
  calc
    IsLocalRing.residue k (Algebra.norm k (Ideal.Quotient.mk q.asIdeal b)) =
        e (Algebra.norm k (E (Ideal.Quotient.mk q.asIdeal b))) :=
      congrArg e (Algebra.norm_eq_of_algEquiv E _).symm
    _ = Algebra.norm (IsLocalRing.ResidueField k)
        (E (Ideal.Quotient.mk q.asIdeal b)) := Algebra.norm_eq_of_ringEquiv e he _
    _ = _ := by rw [hE]

end Algebra

namespace Module

universe u v w

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B] {M : Type w} [AddCommGroup M] [Module B M]
  [Module k M] [IsScalarTower k B M] [Module.Finite k M]

include k in
/-- The source tensor presentation of each local module has finite length. Finiteness
is established before converting the length from extended naturals to naturals. -/
theorem localized_length_ne_top_of_finiteDimensional (q : MaximalSpectrum B) :
    Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⊗[B] M) ≠ ⊤ := by
  let : IsNoetherian B M := isNoetherian_of_tower k inferInstance
  let : IsArtinian B M := isArtinian_of_tower k inferInstance
  rw [← (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M).length_eq]
  exact finiteAlgebra_localized_length_ne_top k B Module.length_ne_top q

/-- The scalar determinant on a finite-dimensional module over a finite algebra is the
product of the norms on the actual maximal quotients, with the actual local lengths.
This is the all-point form of the local scalar calculation in Stacks 0GSZ. -/
@[colib_tag "COL-0183",
  stacks 0GSZ "semilocal finite-algebra product of the local scalar determinant formula"]
theorem det_lsmul_eq_prod_norm_pow_localized_length [Fintype (MaximalSpectrum B)]
    (b : B) :
    ((LinearMap.lsmul B M b).restrictScalars k).det =
      ∏ q : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat := by
  classical
  let : IsNoetherian B M := isNoetherian_of_tower k inferInstance
  let : IsArtinian B M := isArtinian_of_tower k inferInstance
  let L (q : MaximalSpectrum B) := Localization.AtPrime q.asIdeal
  let N (q : MaximalSpectrum B) := LocalizedModule q.asIdeal.primeCompl M
  let : ∀ q : MaximalSpectrum B, IsLocalHom (algebraMap k (L q)) :=
    fun q => Stacks.Length.isLocalHom_algebraMap_localization (A := k) q
  let : ∀ q : MaximalSpectrum B,
      Module.Finite (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField (L q)) :=
    fun q => Stacks.Length.finite_residueField k q
  obtain ⟨e⟩ := Stacks.Length.nonempty_linearEquiv_pi_localizedModule (B := B) M
  let E : M ≃ₗ[k] (∀ q : MaximalSpectrum B, N q) := e.restrictScalars k
  let hM : IsFiniteLength k M := Module.length_ne_top_iff.mp Module.length_ne_top
  let hN (q : MaximalSpectrum B) : IsFiniteLength k (N q) :=
    IsFiniteLength.of_surjective (f := (LinearMap.proj q).comp E.toLinearMap) hM
      ((LinearMap.proj_surjective (R := k) q).comp E.surjective)
  let hPi : IsFiniteLength k (∀ q : MaximalSpectrum B, N q) := E.isFiniteLength hM
  let hLocal (q : MaximalSpectrum B) : IsFiniteLength (L q) (N q) :=
    Module.length_ne_top_iff.mp
      (finiteAlgebra_localized_length_ne_top k B Module.length_ne_top q)
  let f := (LinearMap.lsmul B M b).restrictScalars k
  let φ (q : MaximalSpectrum B) : Module.End k (N q) :=
    (LinearMap.lsmul (L q) (N q) (algebraMap B (L q) b)).restrictScalars k
  have hcomm : E.toLinearMap.comp f = (LinearMap.piMap φ).comp E.toLinearMap := by
    ext m q
    change e (b • m) q = algebraMap B (L q) b • e m q
    simpa only [map_smul, Pi.smul_apply] using
      (IsScalarTower.algebraMap_smul (L q) b (e m q)).symm
  apply (IsLocalRing.residue k).injective
  calc
    IsLocalRing.residue k f.det = FiniteLengthEndomorphism.det k hM f :=
      (FiniteLengthEndomorphism.det_eq_residue_det hM f).symm
    _ = FiniteLengthEndomorphism.det k hPi (LinearMap.piMap φ) :=
      FiniteLengthEndomorphism.det_eq_of_linearEquiv hM hPi f _ E hcomm
    _ = ∏ q : MaximalSpectrum B, FiniteLengthEndomorphism.det k (hN q) (φ q) :=
      FiniteLengthEndomorphism.det_piMap N hN hPi φ
    _ = ∏ q : MaximalSpectrum B,
        Algebra.norm (IsLocalRing.ResidueField k)
            (IsLocalRing.residue (L q) (algebraMap B (L q) b)) ^
          (Module.length (L q) (N q)).toNat := by
      apply Finset.prod_congr rfl
      intro q _
      exact FiniteLengthEndomorphism.multiplication_det_eq_norm_pow_length
        k (L q) (N q) (hLocal q) (algebraMap B (L q) b)
    _ = IsLocalRing.residue k
        (∏ q : MaximalSpectrum B, Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (L q) (N q)).toNat) := by
      simp only [L, map_prod, map_pow, Algebra.residue_norm_quotient_eq_norm_residue]

/-- The intrinsic determinant formula, with no supplied enumeration of the maximal
spectrum. Its finiteness follows from the finite-algebra hypothesis. -/
@[colib_tag "COL-0183"]
theorem det_lsmul_eq_finprod_norm_pow_localized_length (b : B) :
    ((LinearMap.lsmul B M b).restrictScalars k).det =
      ∏ᶠ q : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat := by
  classical
  let : Finite (MaximalSpectrum B) := finiteAlgebra_maximalSpectrum_finite k B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]
  exact det_lsmul_eq_prod_norm_pow_localized_length b

/-- The tensor-localization form of the intrinsic determinant formula. This is the
same localization, through the native tensor comparison. -/
@[colib_tag "COL-0183"]
theorem det_lsmul_eq_finprod_norm_pow_localized_length_tensor (b : B) :
    ((LinearMap.lsmul B M b).restrictScalars k).det =
      ∏ᶠ q : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal ⊗[B] M)).toNat := by
  rw [det_lsmul_eq_finprod_norm_pow_localized_length]
  apply finprod_congr
  intro q
  rw [(LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M).length_eq]

/-- The source's enumerated tensor-localization presentation of the determinant formula. -/
theorem det_lsmul_eq_prod_norm_pow_localized_length_tensor
    [Fintype (MaximalSpectrum B)] (b : B) :
    ((LinearMap.lsmul B M b).restrictScalars k).det =
      ∏ q : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal ⊗[B] M)).toNat := by
  simpa only [finprod_eq_prod_of_fintype] using
    det_lsmul_eq_finprod_norm_pow_localized_length_tensor (k := k) (M := M) b

end Module

namespace Algebra

universe u v

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B]

include k in
/-- Every local ring of a finite-dimensional algebra has finite self-length. -/
theorem local_length_ne_top_of_finite (q : MaximalSpectrum B) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) ≠ ⊤ := by
  rw [← (TensorProduct.AlgebraTensorModule.rid B
    (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).length_eq]
  exact Module.localized_length_ne_top_of_finiteDimensional (k := k) (M := B) q

/-- The determinant norm of a finite algebra is the product of its actual residue-field
norms, weighted by the full lengths of its local rings. No reducedness or separability
is assumed, and the zero algebra is included. -/
@[colib_tag "COL-0183",
  stacks 0GSZ "finite-algebra norm obtained from the local scalar determinant formula"]
theorem norm_eq_prod_quotient_norm_pow_local_length [Fintype (MaximalSpectrum B)]
    (b : B) :
    Algebra.norm k b = ∏ q : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat := by
  have h := Module.det_lsmul_eq_prod_norm_pow_localized_length_tensor
    (k := k) (M := B) b
  have hnorm : (LinearMap.lsmul B B b).restrictScalars k = Algebra.lmul k B b := by
    ext x
    rfl
  rw [hnorm, ← Algebra.norm_apply] at h
  have hlocal (q : MaximalSpectrum B) :
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⊗[B] B) =
        Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (TensorProduct.AlgebraTensorModule.rid B
      (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).length_eq
  simpa only [hlocal] using h

/-- The intrinsic finite-algebra norm formula, with spectrum finiteness derived from
finite-dimensionality rather than supplied as an extra hypothesis. -/
@[colib_tag "COL-0183"]
theorem norm_eq_finprod_quotient_norm_pow_local_length (b : B) :
    Algebra.norm k b = ∏ᶠ q : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat := by
  classical
  let : Finite (MaximalSpectrum B) := Module.finiteAlgebra_maximalSpectrum_finite k B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]
  exact norm_eq_prod_quotient_norm_pow_local_length b

end Algebra

namespace IsLocalRing

universe u

/-- Localization at the maximal ideal of a local ring preserves its self-length,
through the canonical localization algebra map. -/
theorem length_localization_maximalIdeal (B : Type u) [CommRing B] [IsLocalRing B] :
    Module.length (Localization.AtPrime (maximalIdeal B))
      (Localization.AtPrime (maximalIdeal B)) = Module.length B B := by
  let L := Localization.AtPrime (maximalIdeal B)
  let e : B ≃ₐ[B] L :=
    IsLocalization.atUnits B (maximalIdeal B).primeCompl
      (fun x => by simpa using! fun a => a)
  have hs : Function.Surjective (algebraMap B L) := e.surjective
  exact (e.toLinearEquiv.length_eq.trans
    (Module.length_eq_of_surjective (S := B) (R := L) (M := L) hs)).symm

end IsLocalRing

namespace Algebra

universe u v

/-- For a finite local algebra, the product is the norm on its one actual residue
field, raised to the full self-length of the algebra. -/
@[colib_tag "COL-0183"]
theorem norm_eq_quotient_norm_pow_length {k : Type u} {B : Type v}
    [Field k] [CommRing B] [Algebra k B] [Module.Finite k B] [IsLocalRing B] (b : B) :
    Algebra.norm k b =
      Algebra.norm k (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b) ^
        (Module.length B B).toNat := by
  have h := norm_eq_prod_quotient_norm_pow_local_length (k := k) b
  rw [Fintype.prod_unique] at h
  change Algebra.norm k b =
    Algebra.norm k (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b) ^
      (Module.length (Localization.AtPrime (IsLocalRing.maximalIdeal B))
        (Localization.AtPrime (IsLocalRing.maximalIdeal B))).toNat at h
  rwa [IsLocalRing.length_localization_maximalIdeal] at h

end Algebra
