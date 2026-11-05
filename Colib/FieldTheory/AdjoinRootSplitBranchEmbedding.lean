/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Actual branch embeddings into a specified splitting field

Each irreducible branch after coefficient extension has a root in a specified
overfield where the original polynomial splits. Its literal quotient field
therefore embeds into that overfield. The branch degree never increases.
Only the actual polynomial, its irreducibility, and its divisibility are used;
no chosen branch type or monicity assumption is required.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k L Ω : Type*} [Field k] [Field L] [Field Ω]
  [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω]

/-- Every literal scalar branch embeds over the coefficient field in the
specified splitting overfield; its degree is bounded by the original degree. -/
@[colib_tag "COL-0209",
  colib_ref "aglib_principal_euler_pin" "FieldTheory/AdjoinRootSplitBranchEmbedding.lean:33-59"
    "adaptation" "Native AdjoinRoot quotient and polynomial divisibility in the actual field tower"]
theorem nonempty_algHom_branch_of_splits (f : k[X]) (hf : f ≠ 0)
    (hsplit : (f.map (algebraMap k Ω)).Splits)
    (q : L[X]) (hq : Irreducible q) (hqdvd : q ∣ f.map (algebraMap k L)) :
    Nonempty (AdjoinRoot q →ₐ[L] Ω) ∧ q.natDegree ≤ f.natDegree := by
  have hsplitL : ((f.map (algebraMap k L)).map (algebraMap L Ω)).Splits := by
    simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using hsplit
  have hqsplit : (q.map (algebraMap L Ω)).Splits :=
    hsplitL.of_dvd (Polynomial.map_ne_zero (Polynomial.map_ne_zero hf))
      (Polynomial.map_dvd (algebraMap L Ω) hqdvd)
  have hqdegree : (q.map (algebraMap L Ω)).degree ≠ 0 := by
    apply degree_ne_of_natDegree_ne
    rw [natDegree_map]
    exact Nat.ne_of_gt hq.natDegree_pos
  obtain ⟨a, ha⟩ := hqsplit.exists_eval_eq_zero hqdegree
  have hroot : aeval a q = 0 := by
    simpa only [eval_map, aeval_def] using ha
  refine ⟨⟨AdjoinRoot.liftAlgHom q (Algebra.ofId L Ω) a hroot⟩, ?_⟩
  simpa only [natDegree_map] using
    natDegree_le_of_dvd hqdvd (Polynomial.map_ne_zero hf)

end AdjoinRoot
