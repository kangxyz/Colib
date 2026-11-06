/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.FactorContraction
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.PolyResidueRing
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Actual coefficient-factor support

The distinct monic irreducible factors of a coefficient image form an actual finite set of
native closed points. The construction uses the preimage of Mathlib's normalized factors;
repeated factors are not repeated as points. Multiplicities belong in residue coefficients.
For an integral coefficient extension, every target point lies over a source closed point.
For an arbitrary coefficient homomorphism, this holds at every point of nonzero contraction.

No new point, field, norm, residue, or map model is introduced. The field universes are
independent. This file is a source-only draft and has not been compiled.
-/

@[expose] public noncomputable section

open Polynomial UniqueFactorizationMonoid

universe u v

namespace Stacks.Chow.MonicIrreducibleOfDegree

/-- The literal dependent family of native closed points is determined by its polynomial. -/
theorem sigma_poly_injective {k : Type u} [Field k] :
    Function.Injective (fun p : Σ d : ℕ, MonicIrreducibleOfDegree k d => poly p.2) := by
  intro p q h
  obtain ⟨d, p⟩ := p
  obtain ⟨e, q⟩ := q
  change poly p = poly q at h
  obtain rfl : d = e := by rw [← natDegree_eq p, h, natDegree_eq q]
  obtain rfl := poly_injective h
  rfl

/-- The actual coefficient factors of any nonzero polynomial form a finite set. The
membership criterion is divisibility, including repeated factors exactly once as points. -/
theorem exists_finset_mem_iff_dvd_map
    {k : Type u} [Field k] {K : Type v} [Field K]
    (φ : k →+* K) (f : k[X]) (hf : f ≠ 0) :
    ∃ S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree K d),
      ∀ q, q ∈ S ↔ poly q.2 ∣ f.map φ := by
  classical
  let T : Set (Σ d : ℕ, MonicIrreducibleOfDegree K d) :=
    (fun q => poly q.2) ⁻¹' ((normalizedFactors (f.map φ)).toFinset : Set K[X])
  have hT : T.Finite :=
    (normalizedFactors (f.map φ)).toFinset.finite_toSet.preimage
      (fun _ _ _ _ h => sigma_poly_injective h)
  refine ⟨hT.toFinset, ?_⟩
  intro q
  rw [hT.mem_toFinset]
  change poly q.2 ∈ (normalizedFactors (f.map φ)).toFinset ↔ _
  rw [Multiset.mem_toFinset,
    Polynomial.mem_normalizedFactors_iff (Polynomial.map_ne_zero (f := φ) hf)]
  exact ⟨fun h => h.2.2, fun h => ⟨irreducible q.2, monic q.2, h⟩⟩

/-- Every target closed point of an integral coefficient extension lies over a native
source closed point. Over fields this includes every algebraic coefficient extension. -/
theorem exists_dvd_map_of_isIntegral
    {k : Type u} [Field k] {K : Type v} [Field K]
    [Algebra k K] [Algebra.IsIntegral k K]
    {e : ℕ} (q : MonicIrreducibleOfDegree K e) :
    ∃ d : ℕ, ∃ p : MonicIrreducibleOfDegree k d,
      poly q ∣ (poly p).map (algebraMap k K) := by
  obtain ⟨p, hp, hpi, hqp⟩ :=
    (irreducible q).exists_dvd_monic_irreducible_of_isIntegral (K := k)
  exact ⟨p.natDegree, ⟨p, hp, hpi, rfl⟩, hqp⟩

/-- A target point that divides the image of some nonzero polynomial lies over a native
source closed point. Only its root is required to be algebraic; the coefficient extension
itself may be transcendental. -/
theorem exists_dvd_map_of_dvd_map
    {k : Type u} [Field k] {K : Type v} [Field K]
    (φ : k →+* K) {e : ℕ} (q : MonicIrreducibleOfDegree K e)
    (a : k[X]) (ha : a ≠ 0) (hqa : poly q ∣ a.map φ) :
    ∃ d : ℕ, ∃ p : MonicIrreducibleOfDegree k d, poly q ∣ (poly p).map φ := by
  let : Algebra k K := φ.toAlgebra
  let : Fact (Irreducible (poly q)) := ⟨irreducible q⟩
  have hx : IsIntegral k (AdjoinRoot.root (poly q)) := by
    apply IsAlgebraic.isIntegral
    refine ⟨a, ha, ?_⟩
    rw [AdjoinRoot.aeval_eq_of_algebra]
    exact AdjoinRoot.mk_eq_zero.mpr hqa
  have hdvd := minpoly.dvd_map_of_isScalarTower k K (AdjoinRoot.root (poly q))
  rw [AdjoinRoot.minpoly_root (ne_zero q)] at hdvd
  refine ⟨(minpoly k (AdjoinRoot.root (poly q))).natDegree,
    ⟨minpoly k (AdjoinRoot.root (poly q)),
      minpoly.monic hx, minpoly.irreducible hx, rfl⟩, ?_⟩
  exact dvd_of_mul_right_dvd hdvd

/-- The preceding source point generates the literal contracted prime ideal. -/
theorem exists_comap_eq_of_dvd_map
    {k : Type u} [Field k] {K : Type v} [Field K]
    (φ : k →+* K) {e : ℕ} (q : MonicIrreducibleOfDegree K e)
    (a : k[X]) (ha : a ≠ 0) (hqa : poly q ∣ a.map φ) :
    ∃ d : ℕ, ∃ p : MonicIrreducibleOfDegree k d,
      poly q ∣ (poly p).map φ ∧
        (Ideal.span ({poly q} : Set K[X])).comap (Polynomial.mapRingHom φ) =
          Ideal.span ({poly p} : Set k[X]) := by
  obtain ⟨d, p, hqp⟩ := exists_dvd_map_of_dvd_map φ q a ha hqa
  exact ⟨d, p, hqp,
    Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
      (irreducible p) (irreducible q).not_isUnit hqp⟩

end Stacks.Chow.MonicIrreducibleOfDegree

end
