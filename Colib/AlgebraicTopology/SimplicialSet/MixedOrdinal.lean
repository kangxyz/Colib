/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.OrdinalSubdivision
public import Mathlib.Data.Finset.Sort


/-! # Mixed ordinals for the ordinary-subdivision cylinder

A cut selects a terminal segment of an ordinal. The mixed ordinal consists of
one whole copy followed by a second copy of precisely that terminal segment.
It is represented by the corresponding ordered subset of the ordinary join.
-/
/-! Implementation provenance: extracted from `Quillen/Topology/Realization/MixedOrdinal.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, proofs,
assumptions, and universes are retained; only namespaces/imports are migrated.
-/
@[expose] public section


noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.MixedOrdinalCylinder
open SSet.OrdinalSubdivision (δ)
open SSet.OrdinalJoin (left right join_cases)

/-- A monotone map from the simplex ordinal `n` to the two-element ordinal, specifying a
terminal segment. -/
abbrev Cut (n : SimplexCategory) := n ⟶ ⦋1⦌

/-- A vertex of the ordinary join is selected if it is in the whole first copy or in the
terminal segment of the second copy chosen by `φ`. -/
def Selected {n : SimplexCategory} (φ : Cut n)
    (i : Fin ((δ.obj n).len + 1)) : Prop :=
  (∃ j, (left n n).toOrderHom j = i) ∨
    ∃ j, φ.toOrderHom j = 1 ∧ (right n n).toOrderHom j = i

/-- The actual vertices of the mixed ordinal, in their inherited join order. -/
def Vertices {n : SimplexCategory} (φ : Cut n) := {i // Selected φ i}
instance {n : SimplexCategory} (φ : Cut n) : LinearOrder (Vertices φ) := inferInstanceAs
    (LinearOrder (Subtype _))
instance {n : SimplexCategory} (φ : Cut n) : Fintype (Vertices φ) := by classical exact
    inferInstanceAs (Fintype (Subtype _))

/-- The vertex of the mixed ordinal corresponding to `i` in the whole first copy. -/
def firstVertex {n : SimplexCategory} (φ : Cut n) (i : Fin (n.len + 1)) : Vertices φ :=
  ⟨(left n n).toOrderHom i, Or.inl ⟨i, rfl⟩⟩

/-- The vertex of the mixed ordinal corresponding to `i` in the second copy, when the cut sends
`i` to `1`. -/
def repeatVertex {n : SimplexCategory} (φ : Cut n) (i : Fin (n.len + 1))
    (h : φ.toOrderHom i = 1) : Vertices φ :=
  ⟨(right n n).toOrderHom i, Or.inr ⟨i, h, rfl⟩⟩

instance {n : SimplexCategory} (φ : Cut n) : Nonempty (Vertices φ) :=
  ⟨firstVertex φ 0⟩

/-- The skeletal simplex-category representative of the selected ordered subset. -/
def mixedOrdinal {n : SimplexCategory} (φ : Cut n) : SimplexCategory :=
  ⦋Fintype.card (Vertices φ) - 1⦌

/-- Increasing enumeration of all mixed vertices; the set is nonempty. -/
def vertexEquiv {n : SimplexCategory} (φ : Cut n) :
    Fin ((mixedOrdinal φ).len + 1) ≃o Vertices φ :=
  Fintype.orderIsoFinOfCardEq _ (by
    dsimp [mixedOrdinal]
    have := Fintype.card_pos (α := Vertices φ)
    omega)

/-- The first copy is present for every cut. -/
def firstIndex {n : SimplexCategory} (φ : Cut n) : n ⟶ mixedOrdinal φ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ (vertexEquiv φ).symm (firstVertex φ i), by
    intro i j h
    apply (vertexEquiv φ).symm.monotone
    exact h⟩

/-- The ambient inclusion of the selected vertices into the whole join. -/
def inclusion {n : SimplexCategory} (φ : Cut n) : mixedOrdinal φ ⟶ δ.obj n :=
  SimplexCategory.Hom.mk ⟨fun i ↦ (vertexEquiv φ i).val, by
    intro i j h
    exact (vertexEquiv φ).monotone h⟩

@[simp] theorem firstIndex_inclusion {n : SimplexCategory} (φ : Cut n) :
    firstIndex φ ≫ inclusion φ = left n n := by
  ext i : 3
  simp [firstIndex, inclusion, SimplexCategory.comp_toOrderHom, firstVertex]
  rfl

/-- A map of ordinals together with inclusion of the selected terminal segments. -/
def vertexMap {n m : SimplexCategory} {φ : Cut n} {ψ : Cut m}
    (α : n ⟶ m) (h : ∀ i, φ.toOrderHom i ≤ ψ.toOrderHom (α.toOrderHom i)) :
    Vertices φ →o Vertices ψ where
  toFun i := ⟨(δ.map α).toOrderHom i.val, by
    rcases i.property with ⟨j, hj⟩ | ⟨j, hj, hj'⟩
    · rw [← hj]
      exact Or.inl ⟨α.toOrderHom j, (OrdinalSubdivision.δ_map_left α j).symm⟩
    · rw [← hj']
      refine Or.inr ⟨α.toOrderHom j, ?_, (OrdinalSubdivision.δ_map_right α j).symm⟩
      have hh := h j
      rw [hj] at hh
      exact le_antisymm (Fin.le_last _) hh⟩
  monotone' i j hij := (δ.map α).toOrderHom.monotone hij

/-- Mixed reindexing also allows lowering the cut, as needed by the contraction. -/
def mixedMap {n m : SimplexCategory} {φ : Cut n} {ψ : Cut m}
    (α : n ⟶ m) (h : ∀ i, φ.toOrderHom i ≤ ψ.toOrderHom (α.toOrderHom i)) :
    mixedOrdinal φ ⟶ mixedOrdinal ψ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ (vertexEquiv ψ).symm (vertexMap α h (vertexEquiv φ i)),
    (vertexEquiv ψ).symm.monotone.comp ((vertexMap α h).monotone.comp (vertexEquiv φ).monotone)⟩

@[simp] theorem mixedMap_vertex {n m : SimplexCategory} {φ : Cut n} {ψ : Cut m}
    (α : n ⟶ m) (h : ∀ i, φ.toOrderHom i ≤ ψ.toOrderHom (α.toOrderHom i))
    (i : Fin ((mixedOrdinal φ).len + 1)) :
    vertexEquiv ψ ((mixedMap α h).toOrderHom i) = vertexMap α h (vertexEquiv φ i) := by
  simp [mixedMap]

@[simp] theorem mixedMap_id {n : SimplexCategory} (φ : Cut n) :
    mixedMap (φ := φ) (ψ := φ) (𝟙 n) (fun _ ↦ le_rfl) = 𝟙 _ := by
  ext i : 3
  apply (vertexEquiv φ).injective
  apply Subtype.ext
  simp [vertexMap]

@[simp] theorem mixedMap_comp {n m k : SimplexCategory} {φ : Cut n} {ψ : Cut m} {χ : Cut k}
    (α : n ⟶ m) (β : m ⟶ k)
    (h : ∀ i, φ.toOrderHom i ≤ ψ.toOrderHom (α.toOrderHom i))
    (h' : ∀ i, ψ.toOrderHom i ≤ χ.toOrderHom (β.toOrderHom i)) :
    mixedMap α h ≫ mixedMap β h' =
      mixedMap (α ≫ β) (fun i ↦ (h i).trans (h' (α.toOrderHom i))) := by
  ext i : 3
  apply (vertexEquiv χ).injective
  apply Subtype.ext
  simp [SimplexCategory.comp_toOrderHom, vertexMap]

@[simp] theorem firstIndex_naturality {n m : SimplexCategory} {φ : Cut n} {ψ : Cut m}
    (α : n ⟶ m) (h : ∀ i, φ.toOrderHom i ≤ ψ.toOrderHom (α.toOrderHom i)) :
    firstIndex φ ≫ mixedMap α h = α ≫ firstIndex ψ := by
  ext i : 3
  apply (vertexEquiv ψ).injective
  apply Subtype.ext
  simp [SimplexCategory.comp_toOrderHom, firstIndex, vertexMap, firstVertex]

@[simp] theorem mixedMap_inclusion {n m : SimplexCategory} {φ : Cut n} {ψ : Cut m}
    (α : n ⟶ m) (h : ∀ i, φ.toOrderHom i ≤ ψ.toOrderHom (α.toOrderHom i)) :
    mixedMap α h ≫ inclusion ψ = inclusion φ ≫ δ.map α := by
  ext i : 3
  simp [SimplexCategory.comp_toOrderHom, inclusion, vertexMap]


/-- Choose the original or repeated copy according to the cut. -/
def switchedVertex {n : SimplexCategory} (φ : Cut n) (i : Fin (n.len + 1)) : Vertices φ :=
  if h : φ.toOrderHom i = 0 then firstVertex φ i
  else repeatVertex φ i (by
    have hi : (φ.toOrderHom i).val < 2 := (φ.toOrderHom i).isLt
    have hn : (φ.toOrderHom i).val ≠ 0 := fun e ↦ h (Fin.ext e)
    apply Fin.ext
    change (φ.toOrderHom i).val = 1
    omega)

theorem switchedVertex_monotone {n : SimplexCategory} (φ : Cut n) :
    Monotone (switchedVertex φ) := by
  intro i j hij
  dsimp [switchedVertex]
  split_ifs with hi hj hj
  · exact hij
  · change i.val ≤ n.len + 1 + j.val
    have := i.isLt
    omega
  · have h := φ.toOrderHom.monotone hij
    rw [hj] at h
    exact (hi (le_antisymm h (Fin.zero_le _))).elim
  · change n.len + 1 + i.val ≤ n.len + 1 + j.val
    omega

/-- Switch to the repeated copy exactly on the selected terminal segment. -/
def switchedIndex {n : SimplexCategory} (φ : Cut n) : n ⟶ mixedOrdinal φ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ (vertexEquiv φ).symm (switchedVertex φ i),
    (vertexEquiv φ).symm.monotone.comp (switchedVertex_monotone φ)⟩

theorem firstIndex_le_switchedIndex {n : SimplexCategory} (φ : Cut n) (i : Fin (n.len + 1)) :
    (firstIndex φ).toOrderHom i ≤ (switchedIndex φ).toOrderHom i := by
  apply (vertexEquiv φ).symm.monotone
  dsimp [switchedVertex]
  split_ifs
  · exact le_rfl
  · change i.val ≤ n.len + 1 + i.val
    omega

@[simp] theorem switchedIndex_naturality {n m : SimplexCategory} (α : n ⟶ m) (φ : Cut m) :
    switchedIndex (α ≫ φ) ≫ mixedMap α (fun _ ↦ le_rfl) = α ≫ switchedIndex φ := by
  ext i : 3
  apply (vertexEquiv φ).injective
  apply Subtype.ext
  change (vertexEquiv φ ((mixedMap α (fun _ ↦ le_rfl)).toOrderHom
    ((vertexEquiv (α ≫ φ)).symm (switchedVertex (α ≫ φ) i)))).val =
      (vertexEquiv φ ((vertexEquiv φ).symm (switchedVertex φ (α.toOrderHom i)))).val
  rw [mixedMap_vertex, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
  dsimp [switchedVertex]
  split_ifs <;> simp [vertexMap, firstVertex, repeatVertex]

end SSet.MixedOrdinalCylinder
