/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.FactorContraction

/-! Source-only consumers. These examples have not been elaborated. -/

noncomputable section

open Polynomial

universe u v

example {k : Type u} [Field k] {A : Type v} [CommRing A]
    (φ : k →+* A) {p : k[X]} (hp : Irreducible p)
    {q : A[X]} (hq : ¬IsUnit q) (hqp : q ∣ p.map φ) (r : k[X]) :
    q ∣ r.map φ ↔ p ∣ r :=
  dvd_map_iff_of_dvd_irreducible_map φ hp hq hqp r

example {k : Type u} [Field k] {K : Type v} [Field K]
    (φ : k →+* K) {p : k[X]} (hp : Irreducible p)
    {q : K[X]} (hq : Irreducible q) (hqp : q ∣ p.map φ) :
    Ideal.span ({p} : Set k[X]) =
      (Ideal.span ({q} : Set K[X])).comap (Polynomial.mapRingHom φ) :=
  (span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ hp hq.not_isUnit hqp).symm

example {k : Type u} [Field k] {K : Type v} [Field K]
    (φ : k →+* K) {p : k[X]} (hp : Irreducible p)
    {q : K[X]} (hq : Irreducible q) (hqp : q ∣ p.map φ)
    (r : k[X]) (hr : ¬p ∣ r) : ¬q ∣ r.map φ :=
  fun h => hr ((dvd_map_iff_of_dvd_irreducible_map φ hp hq.not_isUnit hqp r).mp h)

end
