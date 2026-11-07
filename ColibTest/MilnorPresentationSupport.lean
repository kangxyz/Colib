/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport

/-!
Consumers of supporting comparisons, not of full presentation independence.
There are no prime-degree, normality, perfectness or characteristic assumptions here.
-/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

example {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (a : (k[X] ⧸ Ideal.span {poly p})ˣ) :
    simpleMilnorNorm q (milnorKRingMap f.toRingHom (milnorKSymbol _ a)) =
      simpleMilnorNorm p (milnorKSymbol _ a) :=
  simpleMilnorNorm_map_algEquiv_symbol p q f a

example {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (z : MilnorKRing k) (a : (k[X] ⧸ Ideal.span {poly p})ˣ) :
    simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p})) z *
          milnorKSymbol _ a)) =
      simpleMilnorNorm p
        (milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p})) z *
          milnorKSymbol _ a) :=
  simpleMilnorNorm_map_algEquiv_mixed p q f z a

example {d e m : ℕ} (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (a : Fin m → kˣ) (b : (k[X] ⧸ Ideal.span {poly p})ˣ) :
    simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (milnorKTupleSymbol (Fin.snoc (Units.map
          (algebraMap k (k[X] ⧸ Ideal.span {poly p})).toMonoidHom ∘ a) b) :
            MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
      simpleMilnorNorm p
        (milnorKTupleSymbol (Fin.snoc (Units.map
          (algebraMap k (k[X] ⧸ Ideal.span {poly p})).toMonoidHom ∘ a) b) :
            MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :=
  simpleMilnorNorm_map_algEquiv_mixedTuple p q f a b

example {d e m : ℕ} (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap k (k[X] ⧸ Ideal.span {poly p})) m) :
    simpleMilnorNorm q
        (milnorKRingMap f.toRingHom (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
      simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :=
  simpleMilnorNorm_map_algEquiv_of_mem_mixedSpan p q f x hx

example (p : MonicIrreducibleOfDegree k 1)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] k)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    simpleMilnorNorm p x = milnorKRingMap f.toRingHom x :=
  simpleMilnorNorm_eq_map_of_degree_one p f x

example (φ : k →+* K) {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree K e) (hq : poly q = (poly p).map φ)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      simpleMilnorNorm q
        (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) (hq ▸ dvd_rfl)) x) :=
  simpleMilnorNorm_map_of_poly_eq_map φ p q hq x

end
