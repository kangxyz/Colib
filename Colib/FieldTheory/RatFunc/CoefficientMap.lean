/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# The existing rational coefficient map on polynomials

These statements use Mathlib's `RatFunc.mapRingHom` directly. No rational-function map or
field model is introduced. Source and target fields have independent universes.

-/

@[expose] public noncomputable section

open Polynomial
open scoped nonZeroDivisors

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K]

namespace Polynomial

/-- An injective coefficient map carries nonzero polynomial denominators to nonzero
denominators. This is the exact input to the existing `RatFunc.mapRingHom`. -/
theorem nonZeroDivisors_le_comap_mapRingHom (φ : k →+* K) :
    k[X]⁰ ≤ K[X]⁰.comap (Polynomial.mapRingHom φ) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (Polynomial.mapRingHom φ)
    (Polynomial.map_injective φ φ.injective)

end Polynomial

namespace RatFunc

/-- The native rational-function map agrees with the supplied polynomial homomorphism on
polynomials. In particular, taking `f = Polynomial.mapRingHom φ` gives actual coefficient change. -/
theorem mapRingHom_algebraMap (f : k[X] →+* K[X]) (hf : k[X]⁰ ≤ K[X]⁰.comap f)
    (p : k[X]) :
    RatFunc.mapRingHom f hf (algebraMap k[X] (RatFunc k) p) =
      algebraMap K[X] (RatFunc K) (f p) := by
  change RatFunc.map f hf (algebraMap k[X] (RatFunc k) p) = _
  simpa only [map_one, div_one] using RatFunc.map_apply_div f hf p 1

end RatFunc

end
