/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.EdgewiseSubdivision
public import Colib.AlgebraicTopology.SimplicialSet.OrdinalJoinDesc
public import Colib.Topology.Realization.HomotopyBridge
public import Mathlib.Topology.Homotopy.Contractible

/-! Explicit contraction of the edgewise subdivision of every representable. -/
/-! Implementation provenance: adapted from `Quillen/Topology/Realization/EdgewiseSimplex.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The genuine reversed
indexing functor, second-half endpoint, proofs, hypotheses and universes are retained.
Shared ordinal joins, diagonal, homotopy gluing and sequential invariance use their
existing native owners; no alternate realization or ordinary subdivision is substituted.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet.EdgewiseSubdivision

open SSet.OrdinalJoin (left right joinDesc joinDesc_left joinDesc_right join_cases)

/-- Decrease first-half endpoints toward zero along a simplicial interval. -/
def contractLeft {p r : SimplexCategory} (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) : p ⟶ r :=
  SimplexCategory.Hom.mk {
    toFun i := if t.toOrderHom i.rev = 0 then s.toOrderHom ((left p p).toOrderHom i) else 0
    monotone' := by
      intro i j hij
      dsimp only
      split_ifs with hi hj hj
      · exact s.toOrderHom.monotone ((left p p).toOrderHom.monotone hij)
      · have ht := t.toOrderHom.monotone (Fin.rev_le_rev.mpr hij)
        rw [hi] at ht
        exact (hj (le_antisymm ht (Fin.zero_le _))).elim
      · exact Fin.zero_le _
      · exact le_rfl }

/-- Increase second-half endpoints toward the last vertex. -/
def contractRight {p r : SimplexCategory} (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) : p ⟶ r :=
  SimplexCategory.Hom.mk {
    toFun i := if t.toOrderHom i = 0 then s.toOrderHom ((right p p).toOrderHom i) else Fin.last
      r.len
    monotone' := by
      intro i j hij
      dsimp only
      split_ifs with hi hj hj
      · exact s.toOrderHom.monotone ((right p p).toOrderHom.monotone hij)
      · exact Fin.le_last _
      · have ht := t.toOrderHom.monotone hij
        rw [hj] at ht
        exact (hi (le_antisymm ht (Fin.zero_le _))).elim
      · exact le_rfl }

/-- The all-degree contraction of an interval-valued simplex toward `(0,n)`. -/
def contractOperator {p r : SimplexCategory} (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) :
    ε.obj p ⟶ r :=
  joinDesc (contractLeft s t) (contractRight s t) (by
    intro i j
    change (if t.toOrderHom i.rev = 0 then _ else _) ≤
      (if t.toOrderHom j = 0 then _ else _)
    split_ifs
    · apply s.toOrderHom.monotone
      change i.val ≤ p.len + 1 + j.val
      omega
    · exact Fin.le_last _
    · exact Fin.zero_le _
    · exact Fin.zero_le _)

@[simp] theorem contractOperator_left {p r : SimplexCategory}
    (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) (i : Fin (p.len + 1)) :
    (contractOperator s t).toOrderHom ((left p p).toOrderHom i) =
      if t.toOrderHom i.rev = 0 then s.toOrderHom ((left p p).toOrderHom i) else 0 :=
  joinDesc_left _ _ _ _

@[simp] theorem contractOperator_right {p r : SimplexCategory}
    (s : ε.obj p ⟶ r) (t : p ⟶ ⦋1⦌) (i : Fin (p.len + 1)) :
    (contractOperator s t).toOrderHom ((right p p).toOrderHom i) =
      if t.toOrderHom i = 0 then s.toOrderHom ((right p p).toOrderHom i) else Fin.last r.len :=
  joinDesc_right _ _ _ _

/-- The contraction commutes with every simplicial operator, including
operators that do not preserve either endpoint. -/
theorem contractOperator_naturality {p q r : SimplexCategory}
    (f : p ⟶ q) (s : ε.obj q ⟶ r) (t : q ⟶ ⦋1⦌) :
    contractOperator (ε.map f ≫ s) (f ≫ t) = ε.map f ≫ contractOperator s t := by
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      contractOperator_left, ε_map_left, Fin.rev_rev]
  · simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      contractOperator_right, ε_map_right]

/-- A simplicial cylinder contracts the subdivision of a standard simplex. -/
def simplexCylinder (n : ℕ) : subdivision (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶
    subdivision (Δ[n] : SSet.{u}) where
  app p := ↾fun z ↦ ULift.up (contractOperator z.1.down z.2.down)
  naturality p q f := by
    ext z : 3
    exact congrArg ULift.up (contractOperator_naturality f.unop z.1.down z.2.down)

/-- The distinguished interval `(0,n)` is a vertex of the subdivided simplex. -/
def simplexVertex (n : ℕ) : subdivision (Δ[n] : SSet.{u}) _⦋0⦌ :=
  ULift.up (joinDesc (⦋0⦌.const ⦋n⦌ 0) (⦋0⦌.const ⦋n⦌ (Fin.last n))
    (fun _ _ ↦ Fin.zero_le _))

@[simp] theorem simplexCylinder_zero (n : ℕ) :
    SSet.ι₀ ≫ simplexCylinder.{u} n = 𝟙 _ := by
  ext p s
  apply congrArg ULift.up
  change contractOperator s.down (p.unop.const ⦋1⦌ 0) = s.down
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp [contractOperator_left, contractOperator_right]

@[simp] theorem simplexCylinder_one (n : ℕ) :
    SSet.ι₁ ≫ simplexCylinder.{u} n = SSet.const (simplexVertex n) := by
  ext p s
  apply congrArg ULift.up
  change contractOperator s.down (p.unop.const ⦋1⦌ 1) =
    ε.map (p.unop.const ⦋0⦌ 0) ≫ (simplexVertex.{u} n).down
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp [contractOperator_left, contractOperator_right, simplexVertex,
      SimplexCategory.comp_toOrderHom, ε_map_left, ε_map_right] <;> rfl

/-- An explicit simplicial contraction of the subdivided standard simplex. -/
def simplexContraction (n : ℕ) :
    SSet.Homotopy (𝟙 (subdivision (Δ[n] : SSet.{u}))) (SSet.const (simplexVertex n)) where
  h := simplexCylinder n
  h₀ := simplexCylinder_zero n
  h₁ := simplexCylinder_one n
  rel := by
    ext p z
    exact z.1.property.elim

/-- The actual geometric realization of an edgewise-subdivided simplex is contractible. -/
theorem contractibleSpace_simplex (n : ℕ) : ContractibleSpace |subdivision (Δ[n] : SSet.{u})| := by
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨realizationPoint (simplexVertex n), ?_⟩
  have h := realizationSimplicialHomotopy (simplexContraction.{u} n)
  have hc : (SSet.toTop.map (SSet.const (X := subdivision (Δ[n] : SSet.{u})) (simplexVertex.{u}
    n))).hom =
      ContinuousMap.const _ (realizationPoint (simplexVertex n)) := by
    ext x
    exact realization_const_apply _ x
  rw [SSet.toTop.map_id, hc] at h
  exact ⟨h⟩

end SSet.EdgewiseSubdivision
