/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Norm.PrimeChosenPresentation
public import Colib.KTheory.MilnorK.Norm.PresentationSupport
public import Colib.KTheory.MilnorK.Symbols.Transport
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Restriction of the chosen norm in purely inseparable prime degree

For a finite purely inseparable extension of prime degree, restricting the actual
chosen Milnor norm back to the extension multiplies every class by the degree.
The selected defining polynomial becomes a power of its single linear factor.
The native scalar-factor formula retains that factor's full multiplicity, and
the degree-one simple norm is the actual quotient evaluation map.

The composite of evaluation, the actual coefficient quotient map, and the
selected algebra equivalence is the identity: pure inseparability identifies
ring homomorphisms once they agree on the base field. Thus no generator equation
for the selected equivalence, arbitrary-presentation norm comparison, general
norm tower law, model, or assumed norm equality is required.

All Milnor fields share one universe. Neither perfectness, characteristic zero,
nor separability is assumed. A trace indexed by a larger fraction-field
automorphism group must retain that original indexing, rather than replace it
by the trivial residue automorphism group.

-/

@[expose] public noncomputable section

open Polynomial Module

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

private theorem minpoly_map_eq_X_sub_C_pow_natDegree_of_isPurelyInseparable
    [IsPurelyInseparable K L] (a : L) :
    (minpoly K a).map (algebraMap K L) = (X - C a) ^ (minpoly K a).natDegree := by
  obtain ⟨n, hn⟩ :=
    IsPurelyInseparable.minpoly_eq_X_sub_C_pow K (ringExpChar K) a
  have hdegree : (minpoly K a).natDegree = ringExpChar K ^ n := by
    have h := congrArg Polynomial.natDegree hn
    simpa only [Polynomial.natDegree_map, Polynomial.natDegree_pow,
      Polynomial.natDegree_X_sub_C, mul_one] using h
  rw [hdegree]
  exact hn

/-- Restriction of the actual chosen norm is multiplication by the extension
degree on the entire native Milnor ring in purely inseparable prime degree. -/
theorem milnorKRingMap_milnorKNormRing_of_isPurelyInseparable_of_prime
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hp : Nat.Prime (finrank K L)) (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K L) (milnorKNormRing K L x) =
      (finrank K L : ℤ) • x := by
  classical
  obtain ⟨a, _ha, e, hdegree, hchosen⟩ :=
    exists_selected_simpleMilnorNorm_presentation_of_prime hp
  let p : MonicIrreducibleOfDegree K (minpoly K a).natDegree :=
    minpolyOfDegree K (Algebra.IsIntegral.isIntegral (R := K) a)
  let q : MonicIrreducibleOfDegree L 1 :=
    ⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩
  have hpmap : (poly p).map (algebraMap K L) = (poly q) ^ finrank K L := by
    change (minpoly K a).map (algebraMap K L) = (X - C a) ^ finrank K L
    rw [← hdegree]
    exact minpoly_map_eq_X_sub_C_pow_natDegree_of_isPurelyInseparable a
  have hq : poly q ∣ (poly p).map (algebraMap K L) := by
    rw [hpmap]
    exact dvd_pow_self (poly q) hp.ne_zero
  have hcover : ∀ (d : ℕ) (r : MonicIrreducibleOfDegree L d),
      poly r ∣ (poly p).map (algebraMap K L) →
        ∃ i ∈ ({PUnit.unit} : Finset PUnit.{1}), poly r = poly q := by
    intro d r hr
    refine ⟨PUnit.unit, Finset.mem_singleton_self _, ?_⟩
    apply Polynomial.eq_of_monic_of_associated (monic r) (monic q)
    apply (irreducible r).associated_of_dvd (irreducible q)
    rw [hpmap] at hr
    exact (irreducible r).prime.dvd_of_dvd_pow hr
  have hmult : multiplicity (poly q) ((poly p).map (algebraMap K L)) =
      finrank K L := by
    rw [hpmap]
    exact multiplicity_pow_self (ne_zero q) (irreducible q).not_isUnit _
  let j : (K[X] ⧸ Ideal.span {poly p}) →+* (L[X] ⧸ Ideal.span {poly q}) :=
    AdjoinRoot.map (algebraMap K L) (poly p) (poly q) hq
  let t : (L[X] ⧸ Ideal.span {poly q}) ≃ₐ[L] L :=
    quotientSpanXSubCAlgEquiv a
  have hcomp : (t.toRingHom.comp j).comp e.toRingHom = RingHom.id L := by
    apply IsPurelyInseparable.injective_comp_algebraMap K L L
    apply RingHom.ext
    intro c
    change t (j (e (algebraMap K L c))) = algebraMap K L c
    rw [e.commutes]
    change t (AdjoinRoot.map (algebraMap K L) (poly p) (poly q) hq
      (AdjoinRoot.of (poly p) c)) = algebraMap K L c
    rw [AdjoinRoot.map_of]
    change t (algebraMap L (L[X] ⧸ Ideal.span {poly q})
      (algebraMap K L c)) = algebraMap K L c
    exact t.commutes (algebraMap K L c)
  have hfactor : milnorKRingMap (algebraMap K L)
      (simpleMilnorNorm p (milnorKRingMap e.toRingHom x)) =
        (finrank K L : ℤ) •
          simpleMilnorNorm q (milnorKRingMap j (milnorKRingMap e.toRingHom x)) := by
    have h := simpleMilnorNorm_map_eq_weighted_sum_of_factors
      (algebraMap K L) p (milnorKRingMap e.toRingHom x)
      ({PUnit.unit} : Finset PUnit.{1}) (fun _ => 1) (fun _ => q)
      (fun i _ j _ _ => Subsingleton.elim i j) (fun _ => hq) hcover
    simpa only [Finset.sum_singleton, hmult] using h
  calc
    milnorKRingMap (algebraMap K L) (milnorKNormRing K L x) =
        milnorKRingMap (algebraMap K L)
          (simpleMilnorNorm p (milnorKRingMap e.toRingHom x)) :=
      congrArg (milnorKRingMap (algebraMap K L)) (hchosen x)
    _ = (finrank K L : ℤ) •
        simpleMilnorNorm q (milnorKRingMap j (milnorKRingMap e.toRingHom x)) := hfactor
    _ = (finrank K L : ℤ) •
        milnorKRingMap t.toRingHom (milnorKRingMap j (milnorKRingMap e.toRingHom x)) := by
      rw [simpleMilnorNorm_eq_map_of_degree_one q t]
    _ = (finrank K L : ℤ) • x := by
      rw [milnorKRingMap_comp_apply, milnorKRingMap_comp_apply, hcomp,
        milnorKRingMap_id_apply]

/-- The restriction-norm formula on every existing homogeneous Milnor group,
including degree zero, with its actual field transport. -/
theorem milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable_of_prime
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hp : Nat.Prime (finrank K L)) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTheoryMap (algebraMap K L) n (milnorKNorm K L n x) =
      (finrank K L : ℤ) • x := by
  rw [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKRingMap_milnorKNormRing_of_isPurelyInseparable_of_prime hp
    (x : MilnorKRing L)

end Stacks.Chow

end
