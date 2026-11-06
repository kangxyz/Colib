/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.SylowFixedField
public import Mathlib.FieldTheory.Perfect

/-!
# Finite simultaneous splitting of a small polynomial family

Over a perfect field, a finite family of nonzero polynomials of degree below
`p` splits over a finite extension of degree prime to `p`. The extension is an
actual intermediate field of the native splitting field of the literal product.

Perfectness supplies separability of that finite algebraic splitting field.
The individual polynomials may have repeated factors. No infinite closure,
alternative field model, or polynomial presentation type is constructed.
-/

@[expose] public noncomputable section

namespace IntermediateField

open Polynomial

variable {k : Type*} [Field k] [PerfectField k]

/-- A prescribed finite family of small nonzero polynomials has a finite
prime-to-`p` splitting subfield inside the splitting field of its actual product.
The empty family and polynomials with repeated factors are permitted. -/
@[colib_tag "COL-0225",
  colib_ref "aglib_principal_euler_pin" "FieldTheory/FiniteCoprimeSplitting.lean:31-43"
    "adaptation"
    "Actual prime-to-p intermediate field splitting a finite small family over a perfect base"]
theorem exists_coprime_splitting_field_of_finset (p : ℕ) [Fact p.Prime]
    (s : Finset k[X]) (hne : ∀ q ∈ s, q ≠ 0) (hsmall : ∀ q ∈ s, q.natDegree < p) :
    ∃ S : IntermediateField k (∏ q ∈ s, q).SplittingField,
      FiniteDimensional k S ∧ p.Coprime (Module.finrank k S) ∧
      ∀ q ∈ s, (q.map (algebraMap k S)).Splits := by
  classical
  let f : k[X] := ∏ q ∈ s, q
  have hf : f ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  let : IsGalois k f.SplittingField := ⟨⟩
  apply exists_coprime_splitting_intermediateField p s hsmall
  intro q hq
  exact (SplittingField.splits f).of_dvd (Polynomial.map_ne_zero hf)
    (Polynomial.map_dvd (algebraMap k f.SplittingField) (Finset.dvd_prod_of_mem id hq))

end IntermediateField
