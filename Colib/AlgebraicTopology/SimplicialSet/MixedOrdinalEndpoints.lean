/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinal


/-! # Constant cuts and their exact mixed-ordinal endpoints -/
/-! Implementation provenance: extracted from
`Quillen/Topology/Realization/MixedOrdinalEndpoints.lean`
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

/-- The constant cut at zero, selecting the first-copy endpoint of the mixed ordinal. -/
def zeroCut (n : SimplexCategory) : Cut n := n.const ⦋1⦌ 0
/-- The constant cut at one, selecting the full join endpoint of the mixed ordinal. -/
def oneCut (n : SimplexCategory) : Cut n := n.const ⦋1⦌ 1

@[simp] theorem comp_zeroCut {n m : SimplexCategory} (α : n ⟶ m) :
    α ≫ zeroCut m = zeroCut n := by ext; rfl
@[simp] theorem comp_oneCut {n m : SimplexCategory} (α : n ⟶ m) :
    α ≫ oneCut m = oneCut n := by ext; rfl

theorem zeroVertex_first (n : SimplexCategory) (i : Vertices (zeroCut n)) :
    ∃ j, (left n n).toOrderHom j = i.val := by
  rcases i.property with h | ⟨j, h, _⟩
  · exact h
  · simp [zeroCut, SimplexCategory.const] at h

/-- At the zero cut, forgetting the first-copy tag recovers the original ordinal. -/
def zeroCollapse (n : SimplexCategory) : mixedOrdinal (zeroCut n) ⟶ n :=
  SimplexCategory.Hom.mk ⟨fun i ↦ ⟨(vertexEquiv (zeroCut n) i).val.val, by
    obtain ⟨j, h⟩ := zeroVertex_first n (vertexEquiv (zeroCut n) i)
    rw [← h]
    exact j.isLt⟩, by
    intro i j h
    exact (vertexEquiv (zeroCut n)).monotone h⟩

@[simp] theorem firstIndex_zeroCollapse (n : SimplexCategory) :
    firstIndex (zeroCut n) ≫ zeroCollapse n = 𝟙 n := by
  ext i : 3
  apply Fin.ext
  simp [firstIndex, zeroCollapse, firstVertex, SimplexCategory.comp_toOrderHom]

@[simp] theorem zeroCollapse_firstIndex (n : SimplexCategory) :
    zeroCollapse n ≫ firstIndex (zeroCut n) = 𝟙 _ := by
  ext i : 3
  apply (vertexEquiv (zeroCut n)).injective
  apply Subtype.ext
  apply Fin.ext
  simp [firstIndex, zeroCollapse, firstVertex, SimplexCategory.comp_toOrderHom]

/-- The zero-cut identification is given by the actual first-copy maps. -/
def zeroIso (n : SimplexCategory) : mixedOrdinal (zeroCut n) ≅ n where
  hom := zeroCollapse n
  inv := firstIndex (zeroCut n)
  hom_inv_id := zeroCollapse_firstIndex n
  inv_hom_id := firstIndex_zeroCollapse n

/-- At the one cut, every vertex of the ordinary join is selected. -/
def oneVertex (n : SimplexCategory) (i : Fin ((δ.obj n).len + 1)) : Vertices (oneCut n) :=
  ⟨i, by
    rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨j, rfl, rfl⟩⟩

/-- The ordinal map from the full join `δ.obj n` to the mixed ordinal at the one cut, assigning
each join vertex its corresponding selected-vertex index. -/
def oneInverse (n : SimplexCategory) : δ.obj n ⟶ mixedOrdinal (oneCut n) :=
  SimplexCategory.Hom.mk ⟨fun i ↦ (vertexEquiv (oneCut n)).symm (oneVertex n i), by
    intro i j h
    exact (vertexEquiv (oneCut n)).symm.monotone h⟩

/-- The one-cut identification is the actual inclusion of all join vertices. -/
def oneIso (n : SimplexCategory) : mixedOrdinal (oneCut n) ≅ δ.obj n where
  hom := inclusion (oneCut n)
  inv := oneInverse n
  hom_inv_id := by
    ext i : 3
    apply (vertexEquiv (oneCut n)).injective
    apply Subtype.ext
    simp [inclusion, oneInverse, oneVertex, SimplexCategory.comp_toOrderHom]
  inv_hom_id := by
    ext i : 3
    simp [inclusion, oneInverse, oneVertex, SimplexCategory.comp_toOrderHom]

@[simp] theorem switchedIndex_zero (n : SimplexCategory) :
    switchedIndex (zeroCut n) = firstIndex (zeroCut n) := by
  ext i : 3
  simp [switchedIndex, firstIndex, switchedVertex, zeroCut, SimplexCategory.const]

@[simp] theorem switchedIndex_one_inclusion (n : SimplexCategory) :
    switchedIndex (oneCut n) ≫ inclusion (oneCut n) = right n n := by
  ext i : 3
  simp [switchedIndex, inclusion, switchedVertex, oneCut, repeatVertex,
    SimplexCategory.const, SimplexCategory.comp_toOrderHom]
  rfl

@[simp] theorem zeroCollapse_naturality {n m : SimplexCategory} (α : n ⟶ m) :
    mixedMap (φ := zeroCut n) (ψ := zeroCut m) α (fun _ ↦ le_rfl) ≫ zeroCollapse m =
      zeroCollapse n ≫ α := by
  apply (cancel_epi (zeroIso n).inv).1
  change firstIndex (zeroCut n) ≫ _ = firstIndex (zeroCut n) ≫ _
  rw [← Category.assoc, firstIndex_naturality, Category.assoc, firstIndex_zeroCollapse,
    Category.comp_id, ← Category.assoc, firstIndex_zeroCollapse, Category.id_comp]

/-- At the one cut, every first-copy vertex precedes every switched vertex. -/
theorem firstIndex_one_le_switchedIndex (n : SimplexCategory) (i j : Fin (n.len + 1)) :
    (firstIndex (oneCut n)).toOrderHom i ≤ (switchedIndex (oneCut n)).toOrderHom j := by
  apply (vertexEquiv (oneCut n)).symm.monotone
  simp only [switchedVertex, oneCut, SimplexCategory.const_apply, one_ne_zero, ↓reduceDIte]
  change i.val ≤ n.len + 1 + j.val
  have := i.isLt
  omega

end SSet.MixedOrdinalCylinder
