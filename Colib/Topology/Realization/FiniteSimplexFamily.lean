/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.Boundary
public import Mathlib.Data.Finset.Union

/-!
# Finite face-closed families of actual singular simplices

The family in each degree is a finite set of actual continuous maps. Equal
singular faces are consequently one index, including when they occur in
different top simplices or at different face positions. A finite set in any
one degree generates a bounded face-closed family by taking restrictions
along every map of its finite vertex sets. Including noninjective vertex
maps is harmless and avoids a separate presentation by face occurrences.
-/

@[expose] public section
noncomputable section


universe u

namespace stdSimplex

variable (Z : Type u) [TopologicalSpace Z]

/-- Degreewise finite sets of actual continuous singular simplices. -/
abbrev FiniteSimplexFamily := ∀ d : ℕ, Finset C(_root_.stdSimplex ℝ (Fin (d + 1)), Z)

variable {Z}

/-- Literal precomposition by the affine map on a simplex's vertices. -/
def singularVertexRestriction {d e : ℕ}
    (σ : C(_root_.stdSimplex ℝ (Fin (e + 1)), Z)) (α : Fin (d + 1) → Fin (e + 1)) :
    C(_root_.stdSimplex ℝ (Fin (d + 1)), Z) :=
  σ.comp ⟨stdSimplex.map α, stdSimplex.continuous_map α⟩

@[simp] theorem singularVertexRestriction_id {d : ℕ}
    (σ : C(_root_.stdSimplex ℝ (Fin (d + 1)), Z)) : singularVertexRestriction σ id = σ := by
  ext x
  exact congrArg σ (stdSimplex.map_id_apply x)

/-- Iterated restrictions are the restriction by the actual composite vertex map. -/
theorem singularVertexRestriction_comp {d e k : ℕ}
    (σ : C(_root_.stdSimplex ℝ (Fin (k + 1)), Z))
    (α : Fin (d + 1) → Fin (e + 1)) (β : Fin (e + 1) → Fin (k + 1)) :
    singularVertexRestriction (singularVertexRestriction σ β) α =
      singularVertexRestriction σ (β ∘ α) := by
  ext x
  exact congrArg σ (stdSimplex.map_comp_apply α β x)

/-- Two orders of taking distinct faces give the same actual singular map. -/
theorem singularVertexRestriction_face_face {d : ℕ}
    (σ : C(_root_.stdSimplex ℝ (Fin (d + 3)), Z)) (i : Fin (d + 3)) (k : Fin (d + 2)) :
    singularVertexRestriction (singularVertexRestriction σ i.succAbove) k.succAbove =
      singularVertexRestriction (singularVertexRestriction σ (i.succAbove k).succAbove)
        (k.predAbove i).succAbove := by
  rw [singularVertexRestriction_comp, singularVertexRestriction_comp]
  congr 1
  funext a
  exact (Fin.succAbove_succAbove_succAbove_predAbove i k a).symm

/-- Face closure is stated using the original increasing standard face maps. -/
def FiniteSimplexFamily.FaceClosed (S : FiniteSimplexFamily Z) : Prop :=
  ∀ d (σ : C(_root_.stdSimplex ℝ (Fin (d + 2)), Z)), σ ∈ S (d + 1) →
    ∀ i : Fin (d + 2), singularVertexRestriction σ i.succAbove ∈ S d

/-- The face index is the actual restricted continuous map with its membership proof. -/
def FiniteSimplexFamily.FaceClosed.face {S : FiniteSimplexFamily Z} (hS : S.FaceClosed)
    {d : ℕ} (σ : {σ // σ ∈ S (d + 1)}) (i : Fin (d + 2)) : {τ // τ ∈ S d} :=
  ⟨singularVertexRestriction σ.val i.succAbove, hS d σ.val σ.property i⟩

/-- Both routes to a shared codimension-two face are literally the same index. -/
theorem FiniteSimplexFamily.FaceClosed.face_face {S : FiniteSimplexFamily Z} (hS : S.FaceClosed)
    {d : ℕ} (σ : {σ // σ ∈ S (d + 2)}) (i : Fin (d + 3)) (k : Fin (d + 2)) :
    hS.face (hS.face σ i) k = hS.face (hS.face σ (i.succAbove k)) (k.predAbove i) :=
  Subtype.ext (singularVertexRestriction_face_face σ.val i k)

/-- No simplex in the family has dimension larger than the stated bound. -/
def FiniteSimplexFamily.Bounded (S : FiniteSimplexFamily Z) (N : ℕ) : Prop :=
  ∀ d, N < d → S d = ∅

/-- All vertex restrictions of a finite set, truncated above its own dimension. -/
def finiteVertexRestrictionClosure {N : ℕ}
    (s : Finset C(_root_.stdSimplex ℝ (Fin (N + 1)), Z)) : FiniteSimplexFamily Z := by
  classical
  exact fun d ↦ if d ≤ N then s.biUnion fun σ ↦
    Finset.univ.image (fun α : Fin (d + 1) → Fin (N + 1) ↦ singularVertexRestriction σ α)
    else ∅

/-- Membership exposes a genuine generating simplex and its actual vertex map. -/
theorem mem_finiteVertexRestrictionClosure {N d : ℕ}
    (s : Finset C(_root_.stdSimplex ℝ (Fin (N + 1)), Z))
    (τ : C(_root_.stdSimplex ℝ (Fin (d + 1)), Z)) :
    τ ∈ finiteVertexRestrictionClosure s d ↔
      d ≤ N ∧ ∃ σ ∈ s, ∃ α : Fin (d + 1) → Fin (N + 1),
        singularVertexRestriction σ α = τ := by
  classical
  by_cases h : d ≤ N <;> simp [finiteVertexRestrictionClosure, h]

/-- Every original generator occurs as itself, rather than an occurrence-labelled copy. -/
theorem mem_finiteVertexRestrictionClosure_self {N : ℕ}
    (s : Finset C(_root_.stdSimplex ℝ (Fin (N + 1)), Z))
    {σ : C(_root_.stdSimplex ℝ (Fin (N + 1)), Z)} (hσ : σ ∈ s) :
    σ ∈ finiteVertexRestrictionClosure s N := by
  rw [mem_finiteVertexRestrictionClosure]
  exact ⟨le_rfl, σ, hσ, id, singularVertexRestriction_id σ⟩

/-- Closure of finite support under actual face maps, including shared equal faces. -/
theorem finiteVertexRestrictionClosure_faceClosed {N : ℕ}
    (s : Finset C(_root_.stdSimplex ℝ (Fin (N + 1)), Z)) :
    (finiteVertexRestrictionClosure s).FaceClosed := by
  intro d σ hσ i
  obtain ⟨hd, τ, hτ, α, rfl⟩ := (mem_finiteVertexRestrictionClosure s σ).mp hσ
  rw [mem_finiteVertexRestrictionClosure]
  exact ⟨by omega, τ, hτ, α ∘ i.succAbove, singularVertexRestriction_comp τ _ _ |>.symm⟩

/-- The finite closure never introduces a simplex above the generator dimension. -/
theorem finiteVertexRestrictionClosure_bounded {N : ℕ}
    (s : Finset C(_root_.stdSimplex ℝ (Fin (N + 1)), Z)) :
    (finiteVertexRestrictionClosure s).Bounded N := by
  intro d hd
  simp [finiteVertexRestrictionClosure, Nat.not_le.mpr hd]

/-- The degreewise union of finite families, merging equal actual maps. -/
def FiniteSimplexFamily.union (S T : FiniteSimplexFamily Z) : FiniteSimplexFamily Z := by
  classical
  exact fun d ↦ S d ∪ T d

/-- Pointwise unions keep actual equality of face indices and remain face closed. -/
theorem FiniteSimplexFamily.faceClosed_union {S T : FiniteSimplexFamily Z}
    (hS : S.FaceClosed) (hT : T.FaceClosed) :
    (S.union T).FaceClosed := by
  classical
  intro d σ hσ i
  rcases Finset.mem_union.mp hσ with hσ | hσ
  · exact Finset.mem_union.mpr (Or.inl (hS d σ hσ i))
  · exact Finset.mem_union.mpr (Or.inr (hT d σ hσ i))

/-- The union is bounded by any common upper bound. -/
theorem FiniteSimplexFamily.bounded_union {S T : FiniteSimplexFamily Z} {N : ℕ}
    (hS : S.Bounded N) (hT : T.Bounded N) :
    (S.union T).Bounded N := by
  classical
  intro d hd
  simp [FiniteSimplexFamily.union, hS d hd, hT d hd]

end stdSimplex
