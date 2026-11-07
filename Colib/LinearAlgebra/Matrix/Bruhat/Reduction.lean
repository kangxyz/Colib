/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.Bruhat.RootUpdate
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.LinearAlgebra.Matrix.Bruhat.Decomposition
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Colib.LinearAlgebra.Matrix.Bruhat.Opposite

/-!
# Reduction

Finite matrix Bruhat reduction over fields, using the native general linear
group, with the original rank hypotheses and signed matrix formulas.

## Implementation provenance

Adapted from `Quillen/Aglib/LinearAlgebra/Matrix/Bruhat/Reduction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native elementary matrix units and
finite matrix stabilization are used directly.
-/

@[expose] public section

/-! ## UpperFactorSplits -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- Split the simple entry from the left of an actual upper-unitriangular matrix. -/
lemma split_simple_upper_left (n : ℕ) (i : Fin n) (V : upperUnipotent F (n + 1)) :
    ∃ V₀ : upperUnipotent F (n + 1),
      (V₀ : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = 0 ∧
      V = simpleUpper F n i
        ((V : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ) * V₀ := by
  let t := (V : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ
  refine ⟨simpleUpper F n i (-t) * V, ?_, ?_⟩
  · rw [upper_adjacent_mul, simpleUpper_entry]
    exact neg_add_cancel t
  · apply Subtype.ext
    change (V : Matrix.GeneralLinearGroup (Fin (n + 1)) F) =
      Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne t *
        (Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (-t) * V)
    rw [← mul_assoc, Matrix.GeneralLinearGroup.elementary_mul_same, add_neg_cancel,
      Matrix.GeneralLinearGroup.elementary_zero, one_mul]

/-- The retained signed W(-1) matrix is the actual inverse of W(1). -/
lemma simpleWeyl_matrix_inverse (n : ℕ) (i : Fin n) :
    monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ (-1)) =
      (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1))⁻¹ := by
  rw [rootWMonomial_neg_one F _ _ i.castSucc_lt_succ.ne, map_inv]

/-- A zero simple entry makes the literal W(1) U W(-1) conjugate upper unitriangular. -/
lemma upper_zero_simple_conjugate (n : ℕ) (i : Fin n)
    (U : upperUnipotent F (n + 1))
    (hz : (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = 0) :
    monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) * U *
        monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ (-1)) ∈
      upperUnipotent F (n + 1) := by
  rw [simpleWeyl_matrix_inverse]
  exact upper_simple_reflection_conjugate F n i
    (rootWMonomial F i.castSucc i.succ (1 : Fˣ)).left U hz

end Matrix.Bruhat

end

end

/-! ## ArbitraryBruhatReduction -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- Actual zero-entry upper remainders preserve all four original Bruhat monomials. -/
theorem bruhatMonomial_simple_padding (n : ℕ) (i k : Fin n)
    (c : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (U V : upperUnipotent F (n + 1))
    (hU : (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = 0)
    (hV : (V : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val k.castSucc k.succ = 0) :
    bruhatMonomial F (n + 1) ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V) =
        bruhatMonomial F (n + 1) c ∧
    bruhatMonomial F (n + 1)
        (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
          ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V)) =
      bruhatMonomial F (n + 1)
        (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) * c) ∧
    bruhatMonomial F (n + 1)
        (((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V) *
          monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) =
      bruhatMonomial F (n + 1)
        (c * monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) ∧
    bruhatMonomial F (n + 1)
        (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
          ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V) *
          monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) =
      bruhatMonomial F (n + 1)
        (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) * c *
          monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) := by
  let L := monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ (1 : Fˣ))
  let L' := monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ (-1 : Fˣ))
  let R := monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1 : Fˣ))
  let R' := monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (1 : Fˣ))
  have hL : L' = L⁻¹ := simpleWeyl_matrix_inverse F n i
  have hR : R = R'⁻¹ := simpleWeyl_matrix_inverse F n k
  let A : upperUnipotent F (n + 1) :=
    ⟨L * U * L', upper_zero_simple_conjugate F n i U hU⟩
  let B : upperUnipotent F (n + 1) :=
    ⟨R' * V * R, upper_zero_simple_conjugate F n k V hV⟩
  have hleft : L * ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V) =
      (A : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * (L * c) * V := by
    change L * ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V) =
      (L * U * L') * (L * c) * V
    rw [hL]
    simp [mul_assoc]
  have hright : ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V) * R =
      (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * (c * R) * B := by
    change ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V) * R =
      U * (c * R) * (R' * V * R)
    rw [hR]
    simp [mul_assoc]
  have hboth : L * ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V) * R =
      (A : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * (L * c * R) * B := by
    change L * ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * c * V) * R =
      (L * U * L') * (L * c * R) * (R' * V * R)
    rw [hL, hR]
    simp [mul_assoc]
  refine ⟨bruhatMonomial_unipotent_invariant F (n + 1) c U V, ?_, ?_, ?_⟩
  · rw [hleft]
    exact bruhatMonomial_unipotent_invariant F (n + 1) (L * c) A V
  · rw [hright]
    exact bruhatMonomial_unipotent_invariant F (n + 1) (c * R) U B
  · rw [hboth]
    exact bruhatMonomial_unipotent_invariant F (n + 1) (L * c * R) A B

/-- Every actual matrix has canonical simple-root padding with two zero-entry remainders. -/
theorem finite_bruhat_simple_factorization (n : ℕ) (i k : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ (u v : F) (U₀ V₀ : upperUnipotent F (n + 1)),
      (U₀ : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = 0 ∧
      (V₀ : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val k.castSucc k.succ = 0 ∧
      g = (U₀ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
        simpleBruhatRepresentative F n i k (bruhatMonomial F (n + 1) g) u v * V₀ := by
  obtain ⟨U, V, hg⟩ := bruhatMonomial_factorization F (n + 1) g
  let u := (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ
  let v := (V : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val k.castSucc k.succ
  obtain ⟨U₀, hzU, hU⟩ := split_simple_upper F n i U
  obtain ⟨V₀, hzV, hV⟩ := split_simple_upper_left F n k V
  change U = U₀ * simpleUpper F n i u at hU
  change V = simpleUpper F n k v * V₀ at hV
  refine ⟨u, v, U₀, V₀, hzU, hzV, ?_⟩
  nth_rw 1 [hg]
  rw [hU, hV]
  simp [simpleBruhatRepresentative, simpleUpper, mul_assoc]

/-- A constructed canonical representative preserves the four original finite Bruhat factors. -/
theorem finite_bruhat_four_monomial_reduction (n : ℕ) (i k : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ (u v : F) (U₀ V₀ : upperUnipotent F (n + 1)),
      (U₀ : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = 0 ∧
      (V₀ : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val k.castSucc k.succ = 0 ∧
      g = (U₀ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
        simpleBruhatRepresentative F n i k (bruhatMonomial F (n + 1) g) u v * V₀ ∧
      bruhatMonomial F (n + 1) g = bruhatMonomial F (n + 1)
        (simpleBruhatRepresentative F n i k (bruhatMonomial F (n + 1) g) u v) ∧
      bruhatMonomial F (n + 1)
          (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) * g) =
        bruhatMonomial F (n + 1)
          (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
            simpleBruhatRepresentative F n i k (bruhatMonomial F (n + 1) g) u v) ∧
      bruhatMonomial F (n + 1)
          (g * monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) =
        bruhatMonomial F (n + 1)
          (simpleBruhatRepresentative F n i k (bruhatMonomial F (n + 1) g) u v *
            monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) ∧
      bruhatMonomial F (n + 1)
          (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) * g *
            monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) =
        bruhatMonomial F (n + 1)
          (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
            simpleBruhatRepresentative F n i k (bruhatMonomial F (n + 1) g) u v *
            monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) := by
  obtain ⟨u, v, U₀, V₀, hzU, hzV, hg⟩ := finite_bruhat_simple_factorization F n i k g
  refine ⟨u, v, U₀, V₀, hzU, hzV, hg, ?_⟩
  have hfour := bruhatMonomial_simple_padding F n i k
    (simpleBruhatRepresentative F n i k (bruhatMonomial F (n + 1) g) u v) U₀ V₀ hzU hzV
  simpa only [← hg] using hfour

end Matrix.Bruhat

end

end
