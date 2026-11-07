/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Chains
public import Colib.Analysis.Convex.StdSimplex.BarycentricSubdivision
public import Colib.Algebra.Homology.OrientedList.Support

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SubdivisionRealization.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Transport-correct realization of oriented affine chains

An affine simplex inside the original parameter simplex is included in the
actual twisted singular chain module. Its coefficient is transported inside
the original simplex, from a fixed anchor to the new first vertex. The boundary
identity below retains this transport, including the zeroth face.
-/

@[expose] public section

open Convexity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open FreeAbelianGroup StdSimplex
open CategoryTheory Limits
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- An actual reparametrized singular simplex, with coefficients transported
entirely inside its original source simplex from a specified anchor. -/
def transportedSimplexTerm (A : System.{u, u} X) {N n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (f : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (N + 1)))) :
    fiber A (σ x) ⟶ chainModule A ⦋n⦌ :=
  simplexTransport A σ x (f (StdSimplex.single 0)) ≫ chainInclusion A (σ.comp f)

/-- Transported affine terms commute with every actual face restriction. -/
@[reassoc]
theorem transportedSimplexTerm_chainMap (A : System.{u, u} X) {N m n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (f : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (N + 1))))
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    transportedSimplexTerm A σ x f ≫ chainMap A α =
      transportedSimplexTerm A σ x
        (f.comp ⟨StdSimplex.map α, StdSimplex.continuous_map ℝ α⟩) := by
  simp only [transportedSimplexTerm, Category.assoc, chainInclusion_chainMap]
  unfold restrictionTransport
  rw [simplexTransport_precomp]
  rw [← Category.assoc, simplexTransport_comp]
  rfl

/-- The actual twisted differential on a transported term is the signed sum
of its transported geometric faces. -/
@[reassoc]
theorem transportedSimplexTerm_d (A : System.{u, u} X) {N n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (f : C(StdSimplex ℝ (Fin (n + 2)), StdSimplex ℝ (Fin (N + 1)))) :
    transportedSimplexTerm A σ x f ≫ (singularChainComplex A).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        transportedSimplexTerm A σ x
          (f.comp ⟨StdSimplex.map (SimplexCategory.δ i),
            StdSimplex.continuous_map ℝ (SimplexCategory.δ i)⟩) := by
  simp [singularChainComplex, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    simplicialModule, SimplicialObject.δ, Preadditive.comp_sum,
    transportedSimplexTerm_chainMap]

/-- The vertices of a list whose length has been checked. -/
def listVertices {P : Type*} {n : ℕ} (l : List P) (hl : l.length = n) : Fin n → P :=
  fun i ↦ l[i.val]'(by omega)

/-- Deleting one list vertex is the same affine face used in the singular boundary. -/
theorem listVertices_eraseIdx {P : Type*} {n : ℕ} (l : List P)
    (hl : l.length = n + 2) (i : Fin (n + 2))
    (he : (l.eraseIdx i.val).length = n + 1) :
    listVertices (l.eraseIdx i.val) he = listVertices l hl ∘ i.succAbove := by
  funext j
  dsimp only [listVertices, Function.comp_apply]
  rw [List.getElem_eraseIdx]
  by_cases hji : j.val < i.val
  · rw [dite_eq_left hji, Fin.succAbove_of_castSucc_lt _ _ hji]
    rfl
  · rw [dite_eq_right hji, Fin.succAbove_of_le_castSucc _ _ (by change i.val ≤ j.val; omega)]
    rfl

/-- One checked oriented affine list, interpreted in the actual local chains. -/
def affineListTerm (A : System.{u, u} X) {N : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1))) (n : ℕ)
    (l : List (StdSimplex ℝ (Fin (N + 1)))) : fiber A (σ x) ⟶ chainModule A ⦋n⦌ :=
  if hl : l.length = n + 1 then
    transportedSimplexTerm A σ x (BarycentricSubdivision.affineSimplex (listVertices l hl))
  else 0

/-- Additive realization of formal affine lists in a specified singular degree. -/
def realizeListChain (A : System.{u, u} X) {N : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1))) (n : ℕ) :
    OrientedList.Chain (StdSimplex ℝ (Fin (N + 1))) →+
      (fiber A (σ x) ⟶ chainModule A ⦋n⦌) :=
  FreeAbelianGroup.lift (affineListTerm A σ x n)

@[simp]
theorem realizeListChain_generator (A : System.{u, u} X) {N : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1))) (n : ℕ)
    (l : List (StdSimplex ℝ (Fin (N + 1)))) :
    realizeListChain A σ x n (OrientedList.generator l) = affineListTerm A σ x n l :=
  FreeAbelianGroup.lift_apply_of _ _

/-- A checked list has exactly its specified transported affine realization. -/
theorem affineListTerm_of_length (A : System.{u, u} X) {N n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (l : List (StdSimplex ℝ (Fin (N + 1)))) (hl : l.length = n + 1) :
    affineListTerm A σ x n l =
      transportedSimplexTerm A σ x (BarycentricSubdivision.affineSimplex (listVertices l hl)) := by
  rw [affineListTerm, dite_eq_left hl]

/-- Alternating list deletion realizes as the genuine twisted singular boundary. -/
theorem affineListTerm_d (A : System.{u, u} X) {N n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (l : List (StdSimplex ℝ (Fin (N + 1)))) (hl : l.length = n + 2) :
    affineListTerm A σ x (n + 1) l ≫ (singularChainComplex A).d (n + 1) n =
      realizeListChain A σ x n
        (OrientedList.boundary (OrientedList.generator l)) := by
  rw [affineListTerm_of_length A σ x l hl, transportedSimplexTerm_d]
  have hbd : OrientedList.boundary (OrientedList.generator l) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        OrientedList.generator (l.eraseIdx i.val) := by
    have haux (m : ℕ) (hm : l.length = m) :
        OrientedList.boundary (OrientedList.generator l) =
          ∑ i : Fin m, (-1 : ℤ) ^ i.val •
            OrientedList.generator (l.eraseIdx i.val) := by
      subst m
      exact OrientedList.boundary_generator_eq_sum l
    exact haux _ hl
  rw [hbd, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, realizeListChain_generator]
  have he : (l.eraseIdx i.val).length = n + 1 := by
    have := List.length_eraseIdx_add_one (l := l) (i := i.val) (by omega)
    omega
  rw [affineListTerm_of_length A σ x (l.eraseIdx i.val) he]
  congr 2
  apply ContinuousMap.ext
  intro z
  change BarycentricSubdivision.affineSimplex (listVertices l hl)
    (StdSimplex.map (SimplexCategory.δ i) z) = _
  rw [BarycentricSubdivision.affineSimplex_map]
  rw [listVertices_eraseIdx l hl i he]
  rfl

/-- Homogeneous formal chains realize compatibly with the original local differential. -/
theorem realizeListChain_boundary (A : System.{u, u} X) {N n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (c : OrientedList.Chain (StdSimplex ℝ (Fin (N + 1))))
    (hc : OrientedList.Homogeneous (n + 2) c) :
    realizeListChain A σ x (n + 1) c ≫ (singularChainComplex A).d (n + 1) n =
      realizeListChain A σ x n (OrientedList.boundary c) := by
  induction hc with
  | zero => simp
  | generator l hl =>
    rw [realizeListChain_generator]
    exact affineListTerm_d A σ x l hl
  | add hc hd ihc ihd => simp only [map_add, Preadditive.add_comp, ihc, ihd]
  | neg hc ihc => simp only [map_neg, Preadditive.neg_comp, ihc]

/-- Changing the anchor and parametrization preserves the original coefficient
transport, with composition performed wholly in the original source simplex. -/
@[reassoc]
theorem transportedSimplexTerm_precomp (A : System.{u, u} X) {N M n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (f : C(StdSimplex ℝ (Fin (M + 1)), StdSimplex ℝ (Fin (N + 1))))
    (y : StdSimplex ℝ (Fin (M + 1)))
    (g : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (M + 1)))) :
    simplexTransport A σ x (f y) ≫ transportedSimplexTerm A (σ.comp f) y g =
      transportedSimplexTerm A σ x (f.comp g) := by
  unfold transportedSimplexTerm
  rw [simplexTransport_precomp, ← Category.assoc, simplexTransport_comp]
  rfl

/-- Mapping a checked list applies the point map to its checked vertex tuple. -/
theorem listVertices_map {P Q : Type*} {n : ℕ} (l : List P) (hl : l.length = n)
    (f : P → Q) (hm : (l.map f).length = n) :
    listVertices (l.map f) hm = f ∘ listVertices l hl := by
  funext i
  simp only [listVertices, List.getElem_map, Function.comp_apply]

/-- Affine realization commutes with a reparametrization of the original simplex,
including the transport from its old anchor to the new anchor. -/
theorem affineListTerm_precomp (A : System.{u, u} X) {N M n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (v : Fin (M + 1) → StdSimplex ℝ (Fin (N + 1)))
    (y : StdSimplex ℝ (Fin (M + 1)))
    (l : List (StdSimplex ℝ (Fin (M + 1)))) :
    simplexTransport A σ x (BarycentricSubdivision.affineSimplex v y) ≫
        affineListTerm A (σ.comp (BarycentricSubdivision.affineSimplex v)) y n l =
      affineListTerm A σ x n (l.map (BarycentricSubdivision.affineSimplex v)) := by
  by_cases hl : l.length = n + 1
  · have hm : (l.map (BarycentricSubdivision.affineSimplex v)).length = n + 1 := by
      simpa only [List.length_map] using hl
    rw [affineListTerm_of_length A _ y l hl, transportedSimplexTerm_precomp,
      affineListTerm_of_length A σ x _ hm, BarycentricSubdivision.affineSimplex_comp,
      listVertices_map l hl _ hm]
  · have hm : (l.map (BarycentricSubdivision.affineSimplex v)).length ≠ n + 1 := by
      simpa only [List.length_map] using hl
    simp only [affineListTerm, dite_eq_right hl, dite_eq_right hm, comp_zero]

/-- The transport-correct affine naturality identity extends to every finite chain. -/
theorem realizeListChain_precomp (A : System.{u, u} X) {N M n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : StdSimplex ℝ (Fin (N + 1)))
    (v : Fin (M + 1) → StdSimplex ℝ (Fin (N + 1)))
    (y : StdSimplex ℝ (Fin (M + 1)))
    (c : OrientedList.Chain (StdSimplex ℝ (Fin (M + 1)))) :
    simplexTransport A σ x (BarycentricSubdivision.affineSimplex v y) ≫
        realizeListChain A (σ.comp (BarycentricSubdivision.affineSimplex v)) y n c =
      realizeListChain A σ x n
        (OrientedList.mapPoints (BarycentricSubdivision.affineSimplex v) c) := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => rw [map_zero, comp_zero, map_zero, map_zero]
  | of l =>
    simp only [realizeListChain_generator, OrientedList.mapPoints_generator]
    exact affineListTerm_precomp A σ x v y l
  | neg l hl => simp only [map_neg, Preadditive.comp_neg, hl]
  | add c d hc hd => simp only [map_add, Preadditive.comp_add, hc, hd]

end FundamentalGroupoid.LocalCoefficients
