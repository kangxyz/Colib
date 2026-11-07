/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Norm.ScalarFactorBaseChange
public import Colib.KTheory.MilnorK.Symbols.SplitMixed
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.DegreeOneNorm

/-!
# Native supporting comparisons for simple-norm presentation independence

An actual algebra equivalence between the polynomial quotient fields identifies the two
simple norms on mixed symbols and their existing integer span. A separate corollary of the
compiled scalar-factor formula treats a coefficient image that remains irreducible.

These supporting statements need neither prime degree, normality nor a perfect field.
They do not claim that every class is mixed, presentation independence on the entire ring,
or a tower law for the chosen native FieldNorm. No map, norm, carrier or model is defined.

-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

/-- Algebra-equivalent polynomial presentations have the same simple norm on a unit symbol.
This uses only the native degree-one formula and invariance of the ordinary field norm. -/
theorem simpleMilnorNorm_map_algEquiv_symbol {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (a : (k[X] ⧸ Ideal.span {poly p})ˣ) :
    simpleMilnorNorm q (milnorKRingMap f.toRingHom (milnorKSymbol _ a)) =
      simpleMilnorNorm p (milnorKSymbol _ a) := by
  rw [milnorKRingMap_milnorKSymbol, simpleMilnorNorm_milnorKSymbol,
    simpleMilnorNorm_milnorKSymbol]
  congr 1
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv f (a : k[X] ⧸ Ideal.span {poly p})

/-- A base-field class followed by one unit symbol has presentation-independent simple norm.
This is a local mixed-symbol comparison, not a generation assertion. -/
theorem simpleMilnorNorm_map_algEquiv_mixed {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (z : MilnorKRing k) (a : (k[X] ⧸ Ideal.span {poly p})ˣ) :
    simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p})) z *
          milnorKSymbol _ a)) =
      simpleMilnorNorm p
        (milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p})) z *
          milnorKSymbol _ a) := by
  have hf : f.toRingHom.comp (algebraMap k (k[X] ⧸ Ideal.span {poly p})) =
      algebraMap k (k[X] ⧸ Ideal.span {poly q}) := RingHom.ext f.commutes
  rw [map_mul, milnorKRingMap_comp_apply, hf, simpleMilnorNorm_map_mul,
    simpleMilnorNorm_map_mul, simpleMilnorNorm_map_algEquiv_symbol]

/-- The same comparison on an existing homogeneous tuple with a base prefix. -/
theorem simpleMilnorNorm_map_algEquiv_mixedTuple {d e m : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (a : Fin m → kˣ) (b : (k[X] ⧸ Ideal.span {poly p})ˣ) :
    simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (milnorKTupleSymbol (Fin.snoc (Units.map
          (algebraMap k (k[X] ⧸ Ideal.span {poly p})).toMonoidHom ∘ a) b) :
            MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
      simpleMilnorNorm p
        (milnorKTupleSymbol (Fin.snoc (Units.map
          (algebraMap k (k[X] ⧸ Ideal.span {poly p})).toMonoidHom ∘ a) b) :
            MilnorKRing (k[X] ⧸ Ideal.span {poly p})) := by
  have htuple :
      (milnorKTupleSymbol (Fin.snoc (Units.map
        (algebraMap k (k[X] ⧸ Ideal.span {poly p})).toMonoidHom ∘ a) b) :
          MilnorKRing (k[X] ⧸ Ideal.span {poly p})) =
        milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p}))
          (milnorKSymbolProd k (List.ofFn a)) * milnorKSymbol _ b := by
    rw [coe_milnorKTupleSymbol, List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
    rw [← List.map_ofFn, milnorKSymbolProd_append, milnorKSymbolProd_singleton]
    exact congrArg
      (fun z : MilnorKRing (k[X] ⧸ Ideal.span {poly p}) => z * milnorKSymbol _ b)
      (milnorKRingMap_milnorKSymbolProd
        (algebraMap k (k[X] ⧸ Ideal.span {poly p})) (List.ofFn a)).symm
  rw [htuple]
  exact simpleMilnorNorm_map_algEquiv_mixed p q f _ b

/-- Actual algebra-equivalent polynomial presentations agree on the existing mixed span.
The membership premise is explicit; it is not global presentation independence. -/
theorem simpleMilnorNorm_map_algEquiv_of_mem_mixedSpan {d e m : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap k (k[X] ⧸ Ideal.span {poly p})) m) :
    simpleMilnorNorm q (milnorKRingMap f.toRingHom (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
      simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) := by
  change x ∈ Submodule.span ℤ _ at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hy
      exact simpleMilnorNorm_map_algEquiv_mixedTuple p q f a b
  | zero => simp only [ZeroMemClass.coe_zero, map_zero]
  | add x y hx hy ihx ihy =>
      change simpleMilnorNorm q (milnorKRingMap f.toRingHom
        ((x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) +
          (y : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) =
            simpleMilnorNorm p ((x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) +
              (y : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))
      rw [map_add, map_add, map_add, ihx, ihy]
  | smul z x hx ih =>
      change simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (z • (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) =
        simpleMilnorNorm p (z • (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))
      rw [map_zsmul, map_zsmul, map_zsmul, ih]

/-- In extension degree one, the whole simple norm is the actual inverse structure map.
This is distinct from the degree-one Milnor-symbol formula used above. -/
theorem simpleMilnorNorm_eq_map_of_degree_one
    (p : MonicIrreducibleOfDegree k 1)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] k)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    simpleMilnorNorm p x = milnorKRingMap f.toRingHom x := by
  have hf : (algebraMap k (k[X] ⧸ Ideal.span {poly p})).comp f.toRingHom =
      RingHom.id (k[X] ⧸ Ideal.span {poly p}) := by
    apply RingHom.ext
    intro a
    apply f.injective
    exact f.commutes (f a)
  have hx : milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p}))
      (milnorKRingMap f.toRingHom x) = x := by
    rw [milnorKRingMap_comp_apply, hf, milnorKRingMap_id_apply]
  calc
    simpleMilnorNorm p x = simpleMilnorNorm p
        (milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p}))
          (milnorKRingMap f.toRingHom x) * 1) := by rw [hx, mul_one]
    _ = milnorKRingMap f.toRingHom x * simpleMilnorNorm p 1 :=
      simpleMilnorNorm_map_mul p _ 1
    _ = milnorKRingMap f.toRingHom x := by
      rw [simpleMilnorNorm_one, Nat.cast_one, one_zsmul, mul_one]

/-- If the actual coefficient image remains irreducible, the compiled scalar-factor sum
has one factor of multiplicity one. No separability or finite-extension assumption is used. -/
theorem simpleMilnorNorm_map_of_poly_eq_map (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hq : poly q = (poly p).map φ)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      simpleMilnorNorm q
        (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) (hq ▸ dvd_rfl)) x) := by
  classical
  have hdiv : poly q ∣ (poly p).map φ := hq ▸ dvd_rfl
  have hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ →
        ∃ i ∈ ({PUnit.unit} : Finset PUnit.{1}), poly r = poly q := by
    intro a r hr
    refine ⟨PUnit.unit, Finset.mem_singleton_self _, ?_⟩
    apply Polynomial.eq_of_monic_of_associated (monic r) (monic q)
    apply (irreducible r).associated_of_dvd (irreducible q)
    simpa only [hq] using hr
  have h := simpleMilnorNorm_map_eq_weighted_sum_of_factors φ p x
    ({PUnit.unit} : Finset PUnit.{1}) (fun _ => e) (fun _ => q)
    (fun i _ j _ _ => Subsingleton.elim i j) (fun _ => hdiv) hcover
  have hm : multiplicity (poly q) ((poly p).map φ) = 1 := by
    rw [← hq]
    exact multiplicity_self
      (FiniteMultiplicity.of_not_isUnit (irreducible q).not_isUnit (irreducible q).ne_zero)
  simpa only [Finset.sum_singleton, hm, Nat.cast_one, one_zsmul] using h

end Stacks.Chow

end
