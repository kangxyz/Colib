/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.AdjoinRootSplitBranchEmbedding
import Colib.FieldTheory.SylowFixedField

/-! Direct consumers retain the actual polynomial, scalar tower, and quotient algebra. -/

noncomputable section

namespace ColibTest.AdjoinRootSplitBranchEmbedding

open Polynomial IntermediateField

variable {k L Ω : Type*} [Field k] [Field L] [Field Ω]

/-- Arbitrary coefficient towers need no finiteness, Galois, characteristic,
perfectness, or monicity assumption to embed the literal quotient algebra. -/
theorem every_scalar_branch [Algebra k L] [Algebra k Ω] [Algebra L Ω]
    [IsScalarTower k L Ω] (f : k[X]) (hf : f ≠ 0)
    (hsplit : (f.map (algebraMap k Ω)).Splits)
    (q : L[X]) (hq : Irreducible q) (hqdvd : q ∣ f.map (algebraMap k L)) :
    Nonempty (AdjoinRoot q →ₐ[L] Ω) ∧ q.natDegree ≤ f.natDegree :=
  AdjoinRoot.nonempty_algHom_branch_of_splits f hf hsplit q hq hqdvd

variable [Algebra k Ω]

/-- The intermediate field is the supplied subfield, not a substituted field model. -/
theorem every_intermediate_branch (S : IntermediateField k Ω)
    (f : k[X]) (hf : f ≠ 0) (hsplit : (f.map (algebraMap k Ω)).Splits)
    (q : S[X]) (hq : Irreducible q) (hqdvd : q ∣ f.map (algebraMap k S)) :
    Nonempty (AdjoinRoot q →ₐ[S] Ω) ∧ q.natDegree ≤ f.natDegree :=
  AdjoinRoot.nonempty_algHom_branch_of_splits f hf hsplit q hq hqdvd

/-- The original monic irreducible divisor scope follows using native proof arguments. -/
theorem monic_intermediate_branch (S : IntermediateField k Ω)
    (f : k[X]) (hf : f ≠ 0) (hsplit : (f.map (algebraMap k Ω)).Splits)
    (q : S[X]) (hqmonic : q.Monic) (hq : Irreducible q)
    (hqdvd : q ∣ f.map (algebraMap k S)) :
    q.Monic ∧ Nonempty (AdjoinRoot q →ₐ[S] Ω) ∧ q.natDegree ≤ f.natDegree :=
  ⟨hqmonic, AdjoinRoot.nonempty_algHom_branch_of_splits f hf hsplit q hq hqdvd⟩

/-- A specified Sylow branch retains its embedding, degree bound, and relative
Galois p-group ambient. Ambient Galoisness over the original base is unnecessary. -/
theorem every_sylow_branch [FiniteDimensional k Ω]
    (p : ℕ) (H : Sylow p (Ω ≃ₐ[k] Ω))
    (f : k[X]) (hf : f ≠ 0) (hsplit : (f.map (algebraMap k Ω)).Splits)
    (q : (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω)))[X]) (hq : Irreducible q)
    (hqdvd : q ∣ f.map (algebraMap k (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))))) :
    Nonempty (AdjoinRoot q →ₐ[fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))] Ω) ∧
      q.natDegree ≤ f.natDegree ∧
      IsPGroup p (Ω ≃ₐ[fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))] Ω) ∧
      IsGalois (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) Ω := by
  let : IsGalois (fixedField (H : Subgroup (Ω ≃ₐ[k] Ω))) Ω :=
    IsGalois.of_fixed_field Ω (H : Subgroup (Ω ≃ₐ[k] Ω))
  obtain ⟨hembedding, hdegree⟩ :=
    AdjoinRoot.nonempty_algHom_branch_of_splits f hf hsplit q hq hqdvd
  exact ⟨hembedding, hdegree, isPGroup_aut_over_sylow_fixedField p H, inferInstance⟩

end ColibTest.AdjoinRootSplitBranchEmbedding
