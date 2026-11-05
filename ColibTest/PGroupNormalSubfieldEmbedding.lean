/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.PGroupNormalSubfieldEmbedding
import Colib.FieldTheory.AdjoinRootSplitBranchEmbedding
import Colib.FieldTheory.SylowFixedField

/-!
# Normal prime subfields of literal Sylow branches

The arbitrary-embedding consumer retains the original field. The composed
consumers retain the specified Sylow subgroup, its literal fixed field, and
the original quotient field `AdjoinRoot q`. The strict upper-degree drop is
measured against the actual branch degree, not the degree of a replacement
field. Ambient Galoisness is used only for the coprime base-degree conclusion.
-/

noncomputable section

namespace ColibTest.PGroupNormalSubfieldEmbedding

open Polynomial IntermediateField

section ArbitraryEmbedding

variable {k E Ω : Type*} [Field k] [Field E] [Field Ω]
  [Algebra k E] [Algebra k Ω] [FiniteDimensional k E]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- The original embedded field contains the normal prime-degree subfield;
there is no characteristic or perfectness assumption. -/
theorem original_field_subfield (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (g : E →ₐ[k] Ω)
    (hE : 1 < Module.finrank k E) :
    ∃ J : IntermediateField k E, Normal k J ∧ Module.finrank k J = p ∧
      Module.finrank J E < Module.finrank k E :=
  IntermediateField.exists_normal_prime_subfield_of_embedding p hG g hE

end ArbitraryEmbedding

section SylowBranch

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [FiniteDimensional k Ω]

/-- A nontrivial literal irreducible factor over the specified Sylow fixed
field has an actual normal degree-`p` subfield inside its original quotient
field. Relative Galoisness follows from the finite fixed-field construction,
so the ambient extension over `k` need not be Galois. -/
theorem sylow_branch_normal_prime_subfield (p : ℕ) [Fact p.Prime]
    (H : Sylow p (Ω ≃ₐ[k] Ω))
    (f : k[X]) (hf : f ≠ 0) (hsplit : (f.map (algebraMap k Ω)).Splits)
    (q : (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω)))[X]) [Fact (Irreducible q)]
    (hqdvd : q ∣ f.map (algebraMap k (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω)))))
    (hqdegree : 1 < q.natDegree) :
    Nonempty (AdjoinRoot q →ₐ[fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))] Ω) ∧
      Module.finrank (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) (AdjoinRoot q) =
        q.natDegree ∧
      q.natDegree ≤ f.natDegree ∧
      ∃ J : IntermediateField (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) (AdjoinRoot q),
        Normal (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) J ∧
        Module.finrank (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) J = p ∧
        Module.finrank J (AdjoinRoot q) < q.natDegree := by
  let S : IntermediateField k Ω := fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))
  have hq : Irreducible q := Fact.out
  let : FiniteDimensional S (AdjoinRoot q) := (AdjoinRoot.powerBasis hq.ne_zero).finite
  let : IsGalois S Ω := IsGalois.of_fixed_field Ω (H : Subgroup (Ω ≃ₐ[k] Ω))
  have hdim : Module.finrank S (AdjoinRoot q) = q.natDegree := by
    rw [(AdjoinRoot.powerBasis hq.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have hnontrivial : 1 < Module.finrank S (AdjoinRoot q) := by
    rwa [hdim]
  obtain ⟨⟨g⟩, hbound⟩ :=
    AdjoinRoot.nonempty_algHom_branch_of_splits f hf hsplit q hq hqdvd
  obtain ⟨J, hnormal, hdegree, hdrop⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_embedding p
      (isPGroup_aut_over_sylow_fixedField p H) g hnontrivial
  refine ⟨⟨g⟩, hdim, hbound, J, hnormal, hdegree, ?_⟩
  rwa [hdim] at hdrop

/-- Degree induction is applied only to the strictly smaller remaining
extension over an actual normal prime-degree subfield of the literal branch. -/
theorem sylow_branch_induction_step (p : ℕ) [Fact p.Prime]
    (H : Sylow p (Ω ≃ₐ[k] Ω))
    (f : k[X]) (hf : f ≠ 0) (hsplit : (f.map (algebraMap k Ω)).Splits)
    (q : (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω)))[X]) [Fact (Irreducible q)]
    (hqdvd : q ∣ f.map (algebraMap k (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω)))))
    (hqdegree : 1 < q.natDegree) (P : ℕ → Prop)
    (ih : ∀ d < q.natDegree, P d) :
    ∃ J : IntermediateField (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) (AdjoinRoot q),
      Normal (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) J ∧
      Module.finrank (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) J = p ∧
      P (Module.finrank J (AdjoinRoot q)) := by
  obtain ⟨_, _, _, J, hnormal, hdegree, hdrop⟩ :=
    sylow_branch_normal_prime_subfield p H f hf hsplit q hqdvd hqdegree
  exact ⟨J, hnormal, hdegree, ih _ hdrop⟩

/-- The complete reduction uses one specified fixed field throughout: its
base degree is coprime to `p`, its upper ambient degree is a `p`-power, the
supplied small polynomial family splits there, and the literal branch has
a normal prime-degree subfield with strictly smaller remaining degree. -/
theorem sylow_branch_normal_prime_subfield_and_splitting [IsGalois k Ω]
    (p : ℕ) [Fact p.Prime] (H : Sylow p (Ω ≃ₐ[k] Ω))
    (s : Finset k[X]) (hsmall : ∀ a ∈ s, a.natDegree < p)
    (hsplitFamily : ∀ a ∈ s, (a.map (algebraMap k Ω)).Splits)
    (f : k[X]) (hf : f ≠ 0) (hsplit : (f.map (algebraMap k Ω)).Splits)
    (q : (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω)))[X]) [Fact (Irreducible q)]
    (hqdvd : q ∣ f.map (algebraMap k (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω)))))
    (hqdegree : 1 < q.natDegree) :
    p.Coprime (Module.finrank k (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω)))) ∧
      (∃ r : ℕ, Module.finrank (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) Ω = p ^ r) ∧
      (∀ a ∈ s,
        (a.map (algebraMap k (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))))).Splits) ∧
      Nonempty (AdjoinRoot q →ₐ[fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))] Ω) ∧
      Module.finrank (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) (AdjoinRoot q) =
        q.natDegree ∧
      q.natDegree ≤ f.natDegree ∧
      ∃ J : IntermediateField (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) (AdjoinRoot q),
        Normal (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) J ∧
        Module.finrank (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) J = p ∧
        Module.finrank J (AdjoinRoot q) < q.natDegree := by
  refine ⟨coprime_finrank_sylow_fixedField p H, finrank_over_sylow_fixedField p H, ?_,
    sylow_branch_normal_prime_subfield p H f hf hsplit q hqdvd hqdegree⟩
  intro a ha
  exact splits_over_sylow_fixedField_of_small_degree p H a
    (hsmall a ha) (hsplitFamily a ha)

end SylowBranch

end ColibTest.PGroupNormalSubfieldEmbedding
