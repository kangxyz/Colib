/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.PGroupNormalSubfield

/-! Direct consumers of the actual fixed field and strict induction step. -/

noncomputable section

namespace ColibTest.PGroupNormalSubfield

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- The chosen subgroup contains the original fixing subgroup, retaining
the actual inclusion of its normal prime-degree fixed field in the input. -/
theorem actual_fixed_field (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (E : IntermediateField k Ω) (hE : E ≠ ⊥) :
    ∃ J : Subgroup (Ω ≃ₐ[k] Ω), E.fixingSubgroup ≤ J ∧ J.Normal ∧ J.index = p ∧
      IntermediateField.fixedField J ≤ E ∧
      Module.finrank k (IntermediateField.fixedField J) = p ∧
      Normal k (IntermediateField.fixedField J) :=
  IntermediateField.exists_normal_prime_fixedField p hG E hE

/-- The induction field is a literal intermediate field of the original E. -/
theorem actual_prime_subfield (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (E : IntermediateField k Ω) (hE : E ≠ ⊥) :
    ∃ L : IntermediateField k E, Normal k L ∧ Module.finrank k L = p ∧
      Module.finrank L E < Module.finrank k E :=
  IntermediateField.exists_normal_prime_subfield_of_isPGroup p hG E hE

/-- A strong-induction hypothesis can be invoked on the actual upper
extension, while the lower extension is normal of prime degree. -/
theorem induction_step (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (E : IntermediateField k Ω) (hE : E ≠ ⊥)
    (P : ℕ → Prop) (hP : ∀ d < Module.finrank k E, P d) :
    ∃ L : IntermediateField k E, Normal k L ∧ Module.finrank k L = p ∧
      P (Module.finrank L E) := by
  obtain ⟨L, hL, hdegree, hlt⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_isPGroup p hG E hE
  exact ⟨L, hL, hdegree, hP _ hlt⟩

end ColibTest.PGroupNormalSubfield
