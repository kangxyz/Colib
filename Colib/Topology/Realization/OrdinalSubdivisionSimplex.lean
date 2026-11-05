/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.OrdinalSubdivision
public import Colib.AlgebraicTopology.SimplicialSet.OrdinalJoinDesc
public import Colib.Topology.Realization.HomotopyBridge
public import Mathlib.Topology.Homotopy.Contractible

/-! # A two-stage contraction of ordinarily subdivided simplices

First lower the first half to zero while keeping the second half fixed.
Then lower the second half to zero. Each stage is a genuine all-degree
simplicial homotopy, natural under every ordinal map.
-/
/-! Implementation provenance: adapted from the matching Quillen file at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual two-stage contraction,
indexing functor, maps, hypotheses and universes are unchanged. Only imports and
namespace ownership change. No global subdivision equivalence is assumed.
-/
@[expose] public section


noncomputable section
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.OrdinalSubdivision
open SSet.OrdinalJoin (left right joinDesc joinDesc_left joinDesc_right join_cases)

/-- Lower a nonnegative ordinal-valued map along a simplicial interval. -/
def lowerMap {p r : SimplexCategory} (s : p ⟶ r) (t : p ⟶ ⦋1⦌) : p ⟶ r :=
  SimplexCategory.Hom.mk {
    toFun i := if t.toOrderHom i = 0 then 0 else s.toOrderHom i
    monotone' := by
      intro i j hij
      dsimp only
      split_ifs with hi hj hj
      · exact le_rfl
      · exact Fin.zero_le _
      · have ht := t.toOrderHom.monotone hij
        rw [hj] at ht
        exact (hi (le_antisymm ht (Fin.zero_le _))).elim
      · exact s.toOrderHom.monotone hij }

/-- The middle stage sets the first half to zero and retains the second half. -/
def zeroFirst {p r : SimplexCategory} (s : δ.obj p ⟶ r) : δ.obj p ⟶ r :=
  joinDesc (p.const r 0) (right p p ≫ s) (fun _ _ ↦ Fin.zero_le _)

/-- The first cylinder runs from the middle stage to the original simplex. -/
def firstOperator {p r : SimplexCategory} (s : δ.obj p ⟶ r) (t : p ⟶ ⦋1⦌) : δ.obj p ⟶ r :=
  joinDesc (lowerMap (left p p ≫ s) t) (right p p ≫ s) (by
    intro i j
    change (if t.toOrderHom i = 0 then 0 else _) ≤ _
    split_ifs
    · exact Fin.zero_le _
    · apply s.toOrderHom.monotone
      change i.val ≤ p.len + 1 + j.val
      have := i.isLt
      omega)

/-- The second cylinder runs from the constant zero simplex to the middle stage. -/
def secondOperator {p r : SimplexCategory} (s : δ.obj p ⟶ r) (t : p ⟶ ⦋1⦌) : δ.obj p ⟶ r :=
  joinDesc (p.const r 0) (lowerMap (right p p ≫ s) t) (fun _ _ ↦ Fin.zero_le _)

@[simp] theorem zeroFirst_left {p r : SimplexCategory} (s : δ.obj p ⟶ r) (i : Fin (p.len + 1)) :
    (zeroFirst s).toOrderHom ((left p p).toOrderHom i) = 0 := joinDesc_left _ _ _ _

@[simp] theorem zeroFirst_right {p r : SimplexCategory} (s : δ.obj p ⟶ r) (i : Fin (p.len + 1)) :
    (zeroFirst s).toOrderHom ((right p p).toOrderHom i) =
      s.toOrderHom ((right p p).toOrderHom i) := joinDesc_right _ _ _ _

@[simp] theorem firstOperator_left {p r : SimplexCategory}
    (s : δ.obj p ⟶ r) (t : p ⟶ ⦋1⦌) (i : Fin (p.len + 1)) :
    (firstOperator s t).toOrderHom ((left p p).toOrderHom i) =
      if t.toOrderHom i = 0 then 0 else s.toOrderHom ((left p p).toOrderHom i) :=
  joinDesc_left _ _ _ _

@[simp] theorem firstOperator_right {p r : SimplexCategory}
    (s : δ.obj p ⟶ r) (t : p ⟶ ⦋1⦌) (i : Fin (p.len + 1)) :
    (firstOperator s t).toOrderHom ((right p p).toOrderHom i) =
      s.toOrderHom ((right p p).toOrderHom i) := joinDesc_right _ _ _ _

@[simp] theorem secondOperator_left {p r : SimplexCategory}
    (s : δ.obj p ⟶ r) (t : p ⟶ ⦋1⦌) (i : Fin (p.len + 1)) :
    (secondOperator s t).toOrderHom ((left p p).toOrderHom i) = 0 := joinDesc_left _ _ _ _

@[simp] theorem secondOperator_right {p r : SimplexCategory}
    (s : δ.obj p ⟶ r) (t : p ⟶ ⦋1⦌) (i : Fin (p.len + 1)) :
    (secondOperator s t).toOrderHom ((right p p).toOrderHom i) =
      if t.toOrderHom i = 0 then 0 else s.toOrderHom ((right p p).toOrderHom i) :=
  joinDesc_right _ _ _ _

/-- The middle stage commutes with every simplicial operator. -/
theorem zeroFirst_naturality {p q r : SimplexCategory} (f : p ⟶ q) (s : δ.obj q ⟶ r) :
    zeroFirst (δ.map f ≫ s) = δ.map f ≫ zeroFirst s := by
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      zeroFirst_left, zeroFirst_right, δ_map_left, δ_map_right]

/-- The first homotopy is natural even for maps that do not preserve endpoints. -/
theorem firstOperator_naturality {p q r : SimplexCategory}
    (f : p ⟶ q) (s : δ.obj q ⟶ r) (t : q ⟶ ⦋1⦌) :
    firstOperator (δ.map f ≫ s) (f ≫ t) = δ.map f ≫ firstOperator s t := by
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      firstOperator_left, firstOperator_right, δ_map_left, δ_map_right]

/-- The second homotopy is likewise natural in every simplicial degree. -/
theorem secondOperator_naturality {p q r : SimplexCategory}
    (f : p ⟶ q) (s : δ.obj q ⟶ r) (t : q ⟶ ⦋1⦌) :
    secondOperator (δ.map f ≫ s) (f ≫ t) = δ.map f ≫ secondOperator s t := by
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      secondOperator_left, secondOperator_right, δ_map_left, δ_map_right]

/-- The intermediate self-map of the subdivided standard simplex. -/
def zeroFirstMap (n : ℕ) : subdivision (Δ[n] : SSet.{u}) ⟶ subdivision (Δ[n] : SSet.{u}) where
  app p := ↾fun z ↦ ULift.up (zeroFirst z.down)
  naturality p q f := by
    ext z : 3
    exact congrArg ULift.up (zeroFirst_naturality f.unop z.down)

/-- The first genuine simplicial cylinder. -/
def firstCylinder (n : ℕ) : subdivision (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ subdivision (Δ[n] : SSet.{u})
    where
  app p := ↾fun z ↦ ULift.up (firstOperator z.1.down z.2.down)
  naturality p q f := by
    ext z : 3
    exact congrArg ULift.up (firstOperator_naturality f.unop z.1.down z.2.down)

/-- The second genuine simplicial cylinder. -/
def secondCylinder (n : ℕ) : subdivision (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ subdivision (Δ[n] :
    SSet.{u}) where
  app p := ↾fun z ↦ ULift.up (secondOperator z.1.down z.2.down)
  naturality p q f := by
    ext z : 3
    exact congrArg ULift.up (secondOperator_naturality f.unop z.1.down z.2.down)

/-- The all-zero pair is the chosen vertex of the subdivided standard simplex. -/
def simplexVertex (n : ℕ) : subdivision (Δ[n] : SSet.{u}) _⦋0⦌ :=
  ULift.up ((δ.obj ⦋0⦌).const ⦋n⦌ 0)

@[simp] theorem firstCylinder_zero (n : ℕ) : SSet.ι₀ ≫ firstCylinder.{u} n = zeroFirstMap n := by
  ext p s
  apply congrArg ULift.up
  change firstOperator s.down (p.unop.const ⦋1⦌ 0) = zeroFirst s.down
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp [firstOperator_left, firstOperator_right, zeroFirst_left, zeroFirst_right]

@[simp] theorem firstCylinder_one (n : ℕ) : SSet.ι₁ ≫ firstCylinder.{u} n = 𝟙 _ := by
  ext p s
  apply congrArg ULift.up
  change firstOperator s.down (p.unop.const ⦋1⦌ 1) = s.down
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp [firstOperator_left, firstOperator_right]

@[simp] theorem secondCylinder_zero (n : ℕ) :
    SSet.ι₀ ≫ secondCylinder.{u} n = SSet.const (simplexVertex n) := by
  ext p s
  apply congrArg ULift.up
  change secondOperator s.down (p.unop.const ⦋1⦌ 0) =
    δ.map (p.unop.const ⦋0⦌ 0) ≫ (simplexVertex.{u} n).down
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp [secondOperator_left, secondOperator_right, simplexVertex,
      SimplexCategory.comp_toOrderHom, δ_map_left, δ_map_right]

@[simp] theorem secondCylinder_one (n : ℕ) : SSet.ι₁ ≫ secondCylinder.{u} n = zeroFirstMap n := by
  ext p s
  apply congrArg ULift.up
  change secondOperator s.down (p.unop.const ⦋1⦌ 1) = zeroFirst s.down
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp [secondOperator_left, secondOperator_right, zeroFirst_left, zeroFirst_right]

/-- The first stage is an actual simplicial homotopy from the middle map to the identity. -/
def firstHomotopy (n : ℕ) : SSet.Homotopy (zeroFirstMap.{u} n) (𝟙 _) where
  h := firstCylinder n
  h₀ := firstCylinder_zero n
  h₁ := firstCylinder_one n
  rel := by ext p z; exact z.1.property.elim

/-- The second stage is an actual simplicial homotopy from the constant map to the middle map. -/
def secondHomotopy (n : ℕ) : SSet.Homotopy (SSet.const (simplexVertex.{u} n)) (zeroFirstMap n) where
  h := secondCylinder n
  h₀ := secondCylinder_zero n
  h₁ := secondCylinder_one n
  rel := by ext p z; exact z.1.property.elim

/-- Realizing and concatenating the two stages contracts the subdivided simplex. -/
theorem contractibleSpace_simplex (n : ℕ) : ContractibleSpace |subdivision (Δ[n] : SSet.{u})| := by
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨realizationPoint (simplexVertex n), ?_⟩
  have h₁ := realizationSimplicialHomotopy (firstHomotopy.{u} n)
  have h₂ := realizationSimplicialHomotopy (secondHomotopy.{u} n)
  have hc : (SSet.toTop.map (SSet.const (X := subdivision (Δ[n] : SSet.{u})) (simplexVertex.{u}
    n))).hom =
      ContinuousMap.const _ (realizationPoint (simplexVertex n)) := by
    ext x
    exact realization_const_apply _ x
  rw [SSet.toTop.map_id] at h₁
  rw [hc] at h₂
  exact ⟨h₁.symm.trans h₂.symm⟩

end SSet.OrdinalSubdivision
