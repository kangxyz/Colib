/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot

/-!
# The native coefficient-factor map on polynomial classes

This is an evaluation lemma for the existing `AdjoinRoot.map`, not a new quotient map.

-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace AdjoinRoot

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- The actual coefficient-factor map sends a polynomial class to its coefficient image. -/
@[simp]
theorem map_mk (φ : R →+* S) (p : R[X]) (q : S[X]) (hqp : q ∣ p.map φ)
    (r : R[X]) :
    AdjoinRoot.map φ p q hqp (AdjoinRoot.mk p r) = AdjoinRoot.mk q (r.map φ) := by
  change AdjoinRoot.lift ((AdjoinRoot.of q).comp φ) (AdjoinRoot.root q) _
    (AdjoinRoot.mk p r) = _
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
  rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

end AdjoinRoot

end
