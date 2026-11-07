/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing elementary subgroups

A bijection of finite index sets induces an isomorphism of matrix unit groups
which carries each elementary generator to the generator with the reindexed
positions. It therefore carries the actual elementary subgroup onto the
elementary subgroup. All statements allow noncommutative coefficient rings.
The map is the native `Units.mapEquiv`, without a second reindexing definition.

Implementation provenance: `Quillen/Aglib/LinearAlgebra/Matrix/ElementaryReindex.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

universe u v w

namespace Matrix.GeneralLinearGroup

variable {R : Type u} [Ring R] {n : Type v} {m : Type w}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma reindex_elementary (e : n ≃ m) (i j : n) (hij : i ≠ j) (a : R) :
    Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv (elementary i j hij a) =
      elementary (e i) (e j) (by simpa using hij) a := by
  apply Units.ext
  change Matrix.reindexRingEquiv R e (1 + Matrix.single i j a) =
    1 + Matrix.single (e i) (e j) a
  rw [map_add, map_one]
  congr 1
  exact Matrix.submatrix_single_equiv e.symm e.symm i j a

lemma reindex_subgroup_le (e : n ≃ m) :
    (elementarySubgroup n R).map
      (Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv).toMonoidHom ≤
        elementarySubgroup m R := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, j, hij, a, rfl⟩
  change Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv
    (elementary i j hij a) ∈ elementarySubgroup m R
  rw [reindex_elementary]
  exact elementary_mem_subgroup _ _ _ _

/-- Reindexing carries the elementary subgroup onto the elementary subgroup. -/
theorem reindex_subgroup (e : n ≃ m) :
    (elementarySubgroup n R).map
      (Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv).toMonoidHom =
        elementarySubgroup m R := by
  apply le_antisymm (reindex_subgroup_le e)
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, j, hij, a, rfl⟩
  have h : e.symm i ≠ e.symm j := by simpa using hij
  refine ⟨elementary (e.symm i) (e.symm j) h a, elementary_mem_subgroup _ _ _ _, ?_⟩
  change Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv
    (elementary (e.symm i) (e.symm j) h a) = elementary i j hij a
  rw [reindex_elementary]
  simp only [Equiv.apply_symm_apply]

end Matrix.GeneralLinearGroup
