/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Contraction of a coefficient factor of an irreducible polynomial

If a nonunit polynomial divides the coefficient image of an irreducible polynomial over a
field, its divisibility test on coefficient images is exactly divisibility by the original
irreducible. This identifies the actual contracted principal ideal. In the field-target,
irreducible-factor case it supplies the equality required by Mathlib's `localRingHom`.

The coefficient target may be any commutative ring, and its universe is independent. No
monicity, separability, finite-extension, localization wrapper, or Milnor theory is used.

-/

@[expose] public noncomputable section

universe u v

namespace Polynomial

variable {k : Type u} [Field k] {A : Type v} [CommRing A]

/-- A nonunit factor of the coefficient image of an irreducible detects precisely the
original irreducible divisibility on every polynomial over the source field. -/
theorem dvd_map_iff_of_dvd_irreducible_map (φ : k →+* A)
    {p : k[X]} (hp : Irreducible p) {q : A[X]} (hq : ¬IsUnit q)
    (hqp : q ∣ p.map φ) (r : k[X]) : q ∣ r.map φ ↔ p ∣ r := by
  constructor
  · intro hqr
    by_contra hpr
    have hc : IsCoprime (p.map φ) (r.map φ) :=
      (hp.coprime_iff_not_dvd.mpr hpr).map (Polynomial.mapRingHom φ)
    exact hq (hc.isUnit_of_dvd' hqp hqr)
  · intro hpr
    exact hqp.trans (Polynomial.map_dvd φ hpr)

/-- The actual principal ideal of a nonunit coefficient factor contracts to the original
irreducible principal ideal. This is equality in the native ideal lattice. -/
theorem span_singleton_comap_mapRingHom_of_dvd_irreducible_map (φ : k →+* A)
    {p : k[X]} (hp : Irreducible p) {q : A[X]} (hq : ¬IsUnit q)
    (hqp : q ∣ p.map φ) :
    (Ideal.span ({q} : Set A[X])).comap (Polynomial.mapRingHom φ) =
      Ideal.span ({p} : Set k[X]) := by
  ext r
  change Polynomial.mapRingHom φ r ∈ Ideal.span ({q} : Set A[X]) ↔
    r ∈ Ideal.span ({p} : Set k[X])
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  exact dvd_map_iff_of_dvd_irreducible_map φ hp hq hqp r

end Polynomial

end
