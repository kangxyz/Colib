/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.StableGeneralLinear.Elementary
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.BlockWhitehead
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.ElementaryReindex

/-!
# Whitehead's lemma for the actual stable general linear group

Finite block factorization proves that the stable elementary subgroup is exactly
its commutator subgroup, hence normal. This holds over every ring, including
noncommutative and zero rings, without a stable-rank or field-size hypothesis.

Implementation provenance: the remaining Whitehead portion of
`Quillen/Algebra/Group/StableElementary.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
universe u
namespace StableGeneralLinear
open scoped commutatorElement
variable (R : Type u) [Ring R]

/-- The stable image of each finite-stage commutator is elementary. -/
lemma of_commutator_mem_elementary (n : ℕ) (g h : Matrix.GeneralLinearGroup (Fin n) R) :
    of R n ⁅g, h⁆ ∈ elementary R := by
  rw [← of_transition R (Nat.le_add_right n n) ⁅g, h⁆]
  apply of_mem_elementary
  have ht : transition R n (n + n) (Nat.le_add_right n n) ⁅g, h⁆ =
      Units.mapEquiv (Matrix.reindexRingEquiv R finSumFinEquiv).toMulEquiv
        (Matrix.GeneralLinearGroup.blockSum ⁅g, h⁆ (1 : Matrix.GeneralLinearGroup (Fin n) R)) := by
    apply Units.ext
    exact transition_val_fromBlocks R n n ⁅g, h⁆
  rw [ht]
  exact Matrix.GeneralLinearGroup.reindex_subgroup_le finSumFinEquiv
    (Subgroup.mem_map_of_mem _ (Matrix.GeneralLinearGroup.blockSum_commutator_mem_subgroup g h))

/-- Every commutator in the stable general linear group is elementary. -/
lemma commutator_le_elementary : commutator (Group R) ≤ elementary R := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro g _ h _
  obtain ⟨n, a, b, rfl, rfl⟩ := exists_of₂ R g h
  rw [← map_commutatorElement]
  exact of_commutator_mem_elementary R n a b

/-- Whitehead's lemma for the actual stable matrix group over an arbitrary ring. -/
theorem elementary_eq_commutator : elementary R = commutator (Group R) :=
  le_antisymm (elementary_le_commutator R) (commutator_le_elementary R)

instance elementary_normal : (elementary R).Normal := by
  rw [elementary_eq_commutator]
  infer_instance

/-- Every perfect subgroup of the stable matrix group lies in its elementary subgroup. -/
theorem perfect_le_elementary (H : Subgroup (Group R)) [_root_.Group.IsPerfect H] :
    H ≤ elementary R := by
  rw [← Subgroup.commutator_eq_self (H := H), elementary_eq_commutator, commutator_def]
  exact Subgroup.commutator_mono le_top le_top

end StableGeneralLinear
