/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.RatFunc.CoefficientMap
import Colib.RingTheory.AdjoinRoot.Map

/-! Source-only consumers of the actual maps. These examples have not been elaborated. -/

noncomputable section

open Polynomial

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K]

example (φ : k →+* K) (p : k[X]) :
    RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
        (algebraMap k[X] (RatFunc k) p) =
      algebraMap K[X] (RatFunc K) (p.map φ) :=
  RatFunc.mapRingHom_algebraMap _ _ p

example (φ : k →+* K) (p q : k[X]) :
    RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
        (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) =
      algebraMap K[X] (RatFunc K) (p.map φ) /
        algebraMap K[X] (RatFunc K) (q.map φ) := by
  rw [map_div₀, RatFunc.mapRingHom_algebraMap, RatFunc.mapRingHom_algebraMap]
  rfl

example (φ : k →+* K) :
    RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
        (algebraMap k[X] (RatFunc k) X) =
      algebraMap K[X] (RatFunc K) X := by
  simpa only [Polynomial.coe_mapRingHom, Polynomial.map_X] using
    RatFunc.mapRingHom_algebraMap (Polynomial.mapRingHom φ)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) X

example {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (φ : R →+* S) (p : R[X]) (q : S[X]) (hqp : q ∣ p.map φ) (r : R[X]) :
    AdjoinRoot.map φ p q hqp (AdjoinRoot.mk p r) = AdjoinRoot.mk q (r.map φ) :=
  AdjoinRoot.map_mk φ p q hqp r

end
