/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRAngularComponent
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRMixedCore
public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import Colib.RingTheory.KTheory.MilnorK.Symbols.SplitMixed

/-!
# The native DVR norm–residue square on the existing mixed span

The supplied exact uniformizer coefficient discharges the arithmetic inputs of the native
shift calculation. This gives the canonical norm–residue square on the existing mixed span,
not on all Milnor classes. Exponent one is unconditional under the finite local DVR hypotheses.
The prime-degree corollary explicitly retains Henselianity and exponent invertibility.
The ramification unit and {-1} two-torsion are retained. No ramification index is cancelled.

-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Chow

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E] {π : R} {ϖ : S}

/-- The exact ordinary coefficient gives the symbol-valued angular norm formula.
The natural subtraction e-1 is converted only after proving e is positive. -/
theorem milnorKSymbol_dvrFracUnitPart_norm_of_exact_coefficient
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (b₀ : Rˣ) (hb₀ : Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) * (b₀ : R))
    (hres : residue R (b₀ : R) =
      (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹) (b : Eˣ) :
    milnorKSymbol (ResidueField R)
        (dvrFracUnitPart hπ (Units.map (Algebra.norm F) b)) =
      (e : ℤ) • milnorKNormRing (ResidueField R) (ResidueField S)
        (milnorKSymbol (ResidueField S) (dvrFracUnitPart hϖ b)) +
      dvrFracOrd hϖ b •
        (((Module.finrank (ResidueField R) (ResidueField S) : ℤ) * ((e : ℤ) - 1)) •
            milnorKNegOne (ResidueField R) -
          milnorKNormRing (ResidueField R) (ResidueField S)
            (milnorKSymbol (ResidueField S) (Units.map (residue S).toMonoidHom u))) := by
  have he0 : e ≠ 0 := by
    intro hz
    have hu : IsUnit (algebraMap R S π) := by
      rw [he, hz, pow_zero, mul_one]
      exact u.isUnit
    exact hπ.not_isUnit (isUnit_of_map_unit (algebraMap R S) π hu)
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
  have hcast : ((Module.finrank (ResidueField R) (ResidueField S) * (e - 1) : ℕ) : ℤ) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) * ((e : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub he1, Nat.cast_one]
  rw [dvrFracUnitPart_norm_of_exact_coefficient R S F E hπ hϖ u e he b₀ hb₀ hres b]
  simp only [milnorKSymbol_mul, ← zpow_natCast, milnorKSymbol_zpow, milnorKSymbol_inv,
    ← milnorKNegOne_eq, hcast, milnorKNormRing_milnorKSymbol, sub_eq_add_neg]

/-- The concrete ring-level mixed square from an actual exact uniformizer coefficient.
No claim is made that these mixed classes generate the original ring. -/
theorem dvrMilnorShiftMap_shift_norm_mixed_of_exact_coefficient
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (b₀ : Rˣ) (hb₀ : Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) * (b₀ : R))
    (hres : residue R (b₀ : R) =
      (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹)
    (z : MilnorKRing F) (b : Eˣ) :
    MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKNormRing F E
        (milnorKRingMap (algebraMap F E) z * milnorKSymbol E b))) =
      milnorKNormRing (ResidueField R) (ResidueField S)
        (MilnorKShift.shift (dvrMilnorShiftMap hϖ
          (milnorKRingMap (algebraMap F E) z * milnorKSymbol E b))) := by
  have hf : ∀ a : R, algebraMap F E (algebraMap R F a) =
      algebraMap S E (algebraMap R S a) := fun a =>
    (IsScalarTower.algebraMap_apply R F E a).symm.trans
      (IsScalarTower.algebraMap_apply R S E a)
  have hκ : ResidueField.map (algebraMap R S) =
      algebraMap (ResidueField R) (ResidueField S) := rfl
  exact dvrMilnorShiftMap_shift_norm_mixed (algebraMap R S) hf hκ hπ hϖ u e he z b
    (dvrFracOrd_norm R S F E hπ hϖ b)
    (milnorKSymbol_dvrFracUnitPart_norm_of_exact_coefficient
      R S F E hπ hϖ u e he b₀ hb₀ hres b)

/-- The canonical norm–residue square on the existing mixed span, conditional only on the
explicit exact uniformizer coefficient in addition to the finite local DVR hypotheses. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exact_coefficient
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (b₀ : Rˣ) (hb₀ : Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) * (b₀ : R))
    (hres : residue R (b₀ : R) =
      (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹)
    (m : ℕ) (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) := by
  rw [dvrMilnorTameSymbol'_eq_of_ramified_identity hπ,
    dvrMilnorTameSymbol'_eq_of_ramified_identity hϖ]
  let A : MilnorKTheory E (m + 1) →+ MilnorKTheory (ResidueField R) m :=
    (dvrMilnorTameSymbol (F := F) hπ m).comp (milnorKNorm F E (m + 1))
  let B : MilnorKTheory E (m + 1) →+ MilnorKTheory (ResidueField R) m :=
    (milnorKNorm (ResidueField R) (ResidueField S) m).comp
      (dvrMilnorTameSymbol (F := E) hϖ m)
  change A x = B x
  change x ∈ Submodule.span ℤ _ at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hy
      have htuple :
          (milnorKTupleSymbol (Fin.snoc
            (Units.map (algebraMap F E).toMonoidHom ∘ a) b) : MilnorKRing E) =
          milnorKRingMap (algebraMap F E) (milnorKSymbolProd F (List.ofFn a)) *
            milnorKSymbol E b := by
        rw [coe_milnorKTupleSymbol, List.ofFn_succ']
        simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
        rw [← List.map_ofFn, milnorKSymbolProd_append, milnorKSymbolProd_singleton]
        exact congrArg (fun z : MilnorKRing E => z * milnorKSymbol E b)
          (milnorKRingMap_milnorKSymbolProd (algebraMap F E) (List.ofFn a)).symm
      apply Subtype.ext
      change MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKNormRing F E
          (milnorKTupleSymbol (Fin.snoc
            (Units.map (algebraMap F E).toMonoidHom ∘ a) b) : MilnorKRing E))) =
        milnorKNormRing (ResidueField R) (ResidueField S)
          (MilnorKShift.shift (dvrMilnorShiftMap hϖ
            (milnorKTupleSymbol (Fin.snoc
              (Units.map (algebraMap F E).toMonoidHom ∘ a) b) : MilnorKRing E)))
      rw [htuple]
      exact dvrMilnorShiftMap_shift_norm_mixed_of_exact_coefficient
        R S F E hπ hϖ u e he b₀ hb₀ hres (milnorKSymbolProd F (List.ofFn a)) b
  | zero => simp only [map_zero]
  | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy]
  | smul n x hx ih => rw [map_zsmul, map_zsmul, ih]

/-- Exponent one gives the canonical mixed-span square without Henselianity or prime degree. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exponent_one
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ)
    (m : ℕ) (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  obtain ⟨b₀, hb₀, hres⟩ :=
    IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_exponent_one
      R S F E hπ hϖ u he
  have he1 : algebraMap R S π = (u : S) * ϖ ^ 1 := by simpa only [pow_one] using he
  apply dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exact_coefficient
    R S F E hπ hϖ u 1 he1 b₀ hb₀ _ m x hx
  simpa only [Nat.sub_self, mul_zero, pow_zero, one_mul] using hres

/-- Prime degree gives the canonical mixed-span square with the actual Henselian/tame
hypotheses needed by the uniformizer coefficient theorem. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_prime_degree
    [HenselianLocalRing S]
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime (Module.finrank F E))
    (m : ℕ) (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  obtain ⟨b₀, hb₀, hres⟩ :=
    IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_prime_degree
      R S F E hπ hϖ u e he heunit hp
  exact dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exact_coefficient
    R S F E hπ hϖ u e he b₀ hb₀ hres m x hx

end Stacks.Chow
