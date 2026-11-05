/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.DiscreteValuationRing.FractionOrder
public import Colib.RingTheory.DiscreteValuationRing.RamificationDegree
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Ordinary field norms multiply native DVR orders by residue degree

For a finite torsion-free extension of DVRs with compatible fraction fields,
the ordinary field norm multiplies `Stacks.Chow.dvrFracOrd` by the actual
residue-field degree. The theorem applies to every fraction-field unit,
including poles. It needs no perfectness, separability, henselianity, prime
field degree, or invertibility of the ramification exponent.

The proof first takes norms of the actual equation `pi = u * varpi^e`.
Ring units have integral unit norms. Taking integer orders gives
`e * ord(norm(varpi)) = [E:F]`. The native degree formula gives `[E:F] = e*f`,
and localness proves e is nonzero. Cancellation is in the integers, not in a
residue field or in a power map. Native fraction-unit decomposition finishes
arbitrary integer orders.

## Source provenance

Adapted from `Aglib/RingTheory/DVRNormValuation.lean`, especially lines 105--160,
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`af15a6a5c883bdbc7a94075e5380ddd41467e9926ebd24d858c56368fdc35da7`.
The original module is `Motivic.Aglib.RingTheory.DVRNormValuation`, with source SHA-256
`7e08e6503d336988192dfe1bf904f8a2f523f9479c316a8bdb66d2ddb28a87e7`.
The original perfect-field-dependent relative-ideal-norm proof is replaced by
native e*f and integer cancellation. The order-log comparison identifies the
original order expression without adding its old `order` or `orderHom` models.
The source's relative-ideal-norm helper is not needed or claimed migrated here.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v w z

namespace Algebra

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E]

/-- The ordinary field norm of a ring unit is the image of its actual integral norm.
Integral closedness of the extension DVR supplies the integral-closure instance. -/
@[colib_tag "COL-0201"]
theorem norm_unitsMap_eq_intNorm (a : Sˣ) :
    Units.map (Algebra.norm F) (Units.map (algebraMap S E).toMonoidHom a) =
      Units.map (algebraMap R F).toMonoidHom (Units.map (Algebra.intNorm R S) a) := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  apply Units.ext
  exact (Algebra.algebraMap_intNorm (K := F) (L := E) (a : S)).symm

end Algebra

namespace Stacks.Chow

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E]
  {π : R} {ϖ : S}

/-- A genuine ring unit has ordinary field norm of native order zero. -/
theorem dvrFracOrd_norm_unitsMap (hπ : Irreducible π) (a : Sˣ) :
    dvrFracOrd hπ
      (Units.map (Algebra.norm F) (Units.map (algebraMap S E).toMonoidHom a)) = 0 := by
  rw [Algebra.norm_unitsMap_eq_intNorm R S F E]
  exact dvrFracOrd_eq_of_eq (u := Units.map (Algebra.intNorm R S) a) (n := 0) hπ
    (by simp)

/-- Taking ordinary norms and native integer orders of the actual uniformizer
relation yields the exact multiplicative integer equation before cancellation. -/
theorem ramification_mul_dvrFracOrd_norm_uniformizer
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (a : Sˣ) (e : ℕ)
    (he : algebraMap R S π = (a : S) * ϖ ^ e) :
    (e : ℤ) * dvrFracOrd hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ)) =
      (Module.finrank F E : ℤ) := by
  have hmap : Units.map (algebraMap F E).toMonoidHom (dvrFracUniformizer F hπ) =
      Units.map (algebraMap S E).toMonoidHom a * dvrFracUniformizer E hϖ ^ e := by
    apply Units.ext
    change algebraMap F E (algebraMap R F π) =
      algebraMap S E (a : S) * algebraMap S E ϖ ^ e
    rw [← IsScalarTower.algebraMap_apply R F E,
      IsScalarTower.algebraMap_apply R S E, he, map_mul, map_pow]
  have hnorm : Units.map (Algebra.norm F)
      (Units.map (algebraMap F E).toMonoidHom (dvrFracUniformizer F hπ)) =
      dvrFracUniformizer F hπ ^ Module.finrank F E := by
    apply Units.ext
    exact Algebra.norm_algebraMap (R := F) (S := E) (dvrFracUniformizer F hπ : F)
  have hord := congrArg (dvrFracOrd hπ) hnorm
  rw [hmap, map_mul, map_pow, dvrFracOrd_mul,
    dvrFracOrd_norm_unitsMap R S F E hπ, dvrFracOrd_pow, dvrFracOrd_pow,
    dvrFracOrd_uniformizer, zero_add, mul_one] at hord
  exact hord

/-- The actual nonzero ramification exponent cancels in the integers. No unit
or invertibility hypothesis is placed on that exponent in either DVR. -/
theorem dvrFracOrd_norm_uniformizer_of_equation
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (a : Sˣ) (e : ℕ)
    (he : algebraMap R S π = (a : S) * ϖ ^ e) :
    dvrFracOrd hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) := by
  let : IsLocalHom (algebraMap R S) := inferInstance
  have he0 : e ≠ 0 := by
    intro hz
    have hu : IsUnit (algebraMap R S π) := by
      rw [he, hz, pow_zero, mul_one]
      exact a.isUnit
    exact hπ.not_isUnit (isUnit_of_map_unit (algebraMap R S) π hu)
  have hez : (e : ℤ) ≠ 0 := by exact_mod_cast he0
  have hord := ramification_mul_dvrFracOrd_norm_uniformizer R S F E hπ hϖ a e he
  have hdegree := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F E hπ hϖ a e he
  rw [hdegree, Nat.cast_mul] at hord
  exact mul_left_cancel₀ hez hord

/-- The norm of any extension uniformizer has order the actual residue degree.
The proof constructs a literal uniformizer equation from the nonzero base image. -/
@[colib_tag "COL-0201"]
theorem dvrFracOrd_norm_uniformizer (hπ : Irreducible π) (hϖ : Irreducible ϖ) :
    dvrFracOrd hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) := by
  have hπmap : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero
  obtain ⟨e, a, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπmap hϖ
  exact dvrFracOrd_norm_uniformizer_of_equation R S F E hπ hϖ a e he

/-- The ordinary field norm multiplies the existing native integer order by
actual residue degree, for arbitrary fraction-field units and all integer orders. -/
@[colib_tag "COL-0201",
  colib_ref "aglib_principal_euler_pin" "RingTheory/DVRNormValuation.lean:105-160"
    "adaptation" "Actual ordinary norm-order endpoint via native degree and integer cancellation"]
theorem dvrFracOrd_norm (hπ : Irreducible π) (hϖ : Irreducible ϖ) (x : Eˣ) :
    dvrFracOrd hπ (Units.map (Algebra.norm F) x) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) * dvrFracOrd hϖ x := by
  obtain ⟨a, ha, -⟩ := exists_eq_unit_mul_zpow hϖ x
  have hx : x = Units.map (algebraMap S E).toMonoidHom a *
      dvrFracUniformizer E hϖ ^ dvrFracOrd hϖ x := by
    apply Units.ext
    simpa using ha
  calc
    dvrFracOrd hπ (Units.map (Algebra.norm F) x) =
        dvrFracOrd hπ (Units.map (Algebra.norm F)
          (Units.map (algebraMap S E).toMonoidHom a *
            dvrFracUniformizer E hϖ ^ dvrFracOrd hϖ x)) :=
      congrArg (fun y => dvrFracOrd hπ (Units.map (Algebra.norm F) y)) hx
    _ = (Module.finrank (ResidueField R) (ResidueField S) : ℤ) * dvrFracOrd hϖ x := by
      rw [map_mul, map_zpow, dvrFracOrd_mul, dvrFracOrd_norm_unitsMap R S F E hπ,
        dvrFracOrd_zpow, dvrFracOrd_norm_uniformizer R S F E hπ hϖ, zero_add, mul_comm]

/-- The nonzero-element form uses the actual native norm and its native nonzero theorem. -/
@[colib_tag "COL-0201"]
theorem dvrFracOrd_norm_mk0 (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (x : E) (hx : x ≠ 0) :
    dvrFracOrd hπ (Units.mk0 (Algebra.norm F x) (Algebra.norm_ne_zero_iff.mpr hx)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) *
        dvrFracOrd hϖ (Units.mk0 x hx) := by
  have hmap : Units.map (Algebra.norm F) (Units.mk0 x hx) =
      Units.mk0 (Algebra.norm F x) (Algebra.norm_ne_zero_iff.mpr hx) := by
    apply Units.ext
    rfl
  simpa only [hmap] using dvrFracOrd_norm R S F E hπ hϖ (Units.mk0 x hx)

/-- The source's literal normalized valuation-log expression follows by comparison
with the selected native order, without creating a second order model. -/
@[colib_tag "COL-0201"]
theorem neg_log_valuation_norm (x : Eˣ) :
    -WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation F
      (Algebra.norm F (x : E))) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) *
        -WithZero.log ((IsDiscreteValuationRing.maximalIdeal S).valuation E (x : E)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  simpa only [dvrFracOrd_eq_neg_log_valuation, Units.coe_map] using
    dvrFracOrd_norm R S F E hπ hϖ x

end Stacks.Chow
