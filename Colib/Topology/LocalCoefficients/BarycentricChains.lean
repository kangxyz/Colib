/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SubdivisionRealization
public import Colib.Analysis.Convex.StdSimplex.BarycentricList

/-!
Adapted from `Quillen/Topology/LocalCoefficients/BarycentricChains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Barycentric subdivision on the actual twisted singular chains

The operator is the affine realization of the explicit recursive coning
construction. Coefficients are transported inside each original simplex;
no triviality of the local system is used.
-/

@[expose] public section

open Convexity

open StdSimplex.BarycentricSubdivision


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open FreeAbelianGroup StdSimplex
open CategoryTheory Limits
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

open StdSimplex.BarycentricSubdivision

variable {X : Type u} [TopologicalSpace X]

/-- The ordered list of all vertices of the standard simplex. -/
def standardVertexList (n : ℕ) : List (StdSimplex ℝ (Fin (n + 1))) :=
  List.ofFn (fun i ↦ StdSimplex.single i)

@[simp]
theorem standardVertexList_length (n : ℕ) : (standardVertexList n).length = n + 1 := by
  simp [standardVertexList]

/-- The single original oriented parameter simplex. -/
def standardVertexChain (n : ℕ) :
    OrientedList.Chain (StdSimplex ℝ (Fin (n + 1))) :=
  OrientedList.generator (standardVertexList n)

/-- The standard simplicial operator, as a genuine continuous simplex map. -/
def simplexOperatorMap {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    C(StdSimplex ℝ (Fin (m + 1)), StdSimplex ℝ (Fin (n + 1))) :=
  ⟨StdSimplex.map α, StdSimplex.continuous_map ℝ α⟩

/-- Simplicial operators are exactly the affine maps on their vertex maps. -/
theorem affineSimplex_operator {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    affineSimplex (fun i ↦ (StdSimplex.single (α i) : StdSimplex ℝ (Fin (n + 1)))) =
      simplexOperatorMap α := by
  apply ContinuousMap.ext
  intro x
  simpa only [Function.comp_def, affineSimplex_identity, ContinuousMap.id_apply,
    simplexOperatorMap, ContinuousMap.coe_mk] using
    (affineSimplex_map (fun i : Fin (n + 1) ↦ StdSimplex.single i) α x).symm

/-- Reconstructing a list from its checked vertex function loses no information. -/
theorem ofFn_listVertices {P : Type*} {n : ℕ} (l : List P) (hl : l.length = n) :
    List.ofFn (listVertices l hl) = l := by
  subst n
  exact List.ofFn_getElem

@[simp]
theorem listVertices_ofFn {P : Type*} {n : ℕ} (v : Fin n → P)
    (h : (List.ofFn v).length = n) : listVertices (List.ofFn v) h = v := by
  funext i
  simp [listVertices]

/-- Deleting a vertex of an actual tuple is its ordered simplicial face. -/
theorem eraseIdx_ofFn {P : Type*} {n : ℕ} (v : Fin (n + 2) → P) (i : Fin (n + 2)) :
    (List.ofFn v).eraseIdx i.val = List.ofFn (v ∘ i.succAbove) := by
  have hl : (List.ofFn v).length = n + 2 := List.length_ofFn
  have he : ((List.ofFn v).eraseIdx i.val).length = n + 1 := by
    have := List.length_eraseIdx_add_one (l := List.ofFn v) (i := i.val)
      (by rw [List.length_ofFn]; exact i.isLt)
    omega
  rw [← ofFn_listVertices _ he, listVertices_eraseIdx _ hl i he, listVertices_ofFn]

/-- The face of the original vertex list is its actual mapped lower vertex list. -/
theorem standardVertexList_face {n : ℕ} (i : Fin (n + 2)) :
    (standardVertexList (n + 1)).eraseIdx i.val =
      (standardVertexList n).map (simplexOperatorMap (SimplexCategory.δ i)) := by
  rw [standardVertexList, eraseIdx_ofFn, standardVertexList, List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply, simplexOperatorMap, ContinuousMap.coe_mk,
    StdSimplex.map_single, SimplexCategory.coe_δ]

/-- The original parameter simplex has the usual actual oriented boundary. -/
theorem standardVertexChain_boundary (n : ℕ) :
    OrientedList.boundary (standardVertexChain (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        OrientedList.mapPoints (simplexOperatorMap (SimplexCategory.δ i))
          (standardVertexChain n) := by
  unfold standardVertexChain
  rw [OrientedList.boundary_generator_eq_sum]
  rw [standardVertexList_length]
  apply Finset.sum_congr rfl
  intro i _
  rw [OrientedList.mapPoints_generator, standardVertexList_face]

/-- Barycentric subdivision is natural under the actual face maps. -/
theorem subdivideListChain_operator {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (c : OrientedList.Chain (StdSimplex ℝ (Fin (m + 1)))) :
    OrientedList.mapPoints (simplexOperatorMap α)
        (OrientedList.subdivision listBarycenter c) =
      OrientedList.subdivision listBarycenter
        (OrientedList.mapPoints (simplexOperatorMap α) c) := by
  apply OrientedList.mapPoints_subdivision
  intro l hl
  have h := listBarycenter_natural l hl
    (fun i ↦ (StdSimplex.single (α i) : StdSimplex ℝ (Fin (n + 1))))
  rw [affineSimplex_operator] at h
  exact h.symm

/-- The explicitly subdivided standard parameter simplex. -/
def subdividedStandardChain (n : ℕ) :
    OrientedList.Chain (StdSimplex ℝ (Fin (n + 1))) :=
  OrientedList.subdivision listBarycenter (standardVertexChain n)

/-- Its boundary is the signed sum of the actually subdivided faces. -/
theorem subdividedStandardChain_boundary (n : ℕ) :
    OrientedList.boundary (subdividedStandardChain (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        OrientedList.mapPoints (simplexOperatorMap (SimplexCategory.δ i))
          (subdividedStandardChain n) := by
  unfold subdividedStandardChain
  rw [OrientedList.boundary_subdivision, standardVertexChain_boundary]
  simp only [map_sum, map_zsmul, ← subdivideListChain_operator]

/-- The constructed subdivision preserves the actual degree. -/
theorem subdividedStandardChain_homogeneous (n : ℕ) :
    OrientedList.Homogeneous (n + 1) (subdividedStandardChain n) := by
  apply OrientedList.Homogeneous.subdivision
  exact OrientedList.Supported.generator _ (standardVertexList_length n)

/-- Barycentric subdivision of the actual twisted singular chain module. -/
def barycentricSubdivisionMap (A : System.{u, u} X) (n : ℕ) :
    chainModule A ⦋n⦌ ⟶ chainModule A ⦋n⦌ :=
  Sigma.desc fun σ ↦ realizeListChain A σ (StdSimplex.single 0) n (subdividedStandardChain n)

@[reassoc (attr := simp)]
theorem chainInclusion_barycentricSubdivisionMap (A : System.{u, u} X) (n : ℕ)
    (σ : SingularSimplex X ⦋n⦌) :
    chainInclusion A σ ≫ barycentricSubdivisionMap A n =
      realizeListChain A σ (StdSimplex.single 0) n (subdividedStandardChain n) :=
  Sigma.ι_comp_desc _ _

/-- Realization along a simplicial operator uses exactly the original restriction transport. -/
theorem realizeListChain_operator (A : System.{u, u} X) {N M n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (α : ⦋M⦌ ⟶ ⦋N⦌)
    (c : OrientedList.Chain (StdSimplex ℝ (Fin (M + 1)))) :
    restrictionTransport A σ α ≫
        realizeListChain A (restrictSimplex σ α) (StdSimplex.single 0) n c =
      realizeListChain A σ (StdSimplex.single 0) n
        (OrientedList.mapPoints (simplexOperatorMap α) c) := by
  have h := realizeListChain_precomp (n := n) A σ (StdSimplex.single 0)
    (fun j ↦ (StdSimplex.single (α j) : StdSimplex ℝ (Fin (N + 1))))
    (StdSimplex.single 0) c
  rw [affineSimplex_operator] at h
  exact h

/-- The genuinely constructed barycentric operator commutes with the original
local-coefficient differential in every degree. -/
@[reassoc]
theorem barycentricSubdivisionMap_d (A : System.{u, u} X) (n : ℕ) :
    barycentricSubdivisionMap A (n + 1) ≫ (singularChainComplex A).d (n + 1) n =
      (singularChainComplex A).d (n + 1) n ≫ barycentricSubdivisionMap A n := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion A σ ≫ (_ ≫ _) = chainInclusion A σ ≫ (_ ≫ _)
  rw [chainInclusion_barycentricSubdivisionMap_assoc, chainInclusion_d_assoc,
    realizeListChain_boundary A σ (StdSimplex.single 0) _
      (subdividedStandardChain_homogeneous (n + 1)), subdividedStandardChain_boundary,
    map_sum]
  simp only [map_zsmul, Preadditive.sum_comp, Preadditive.zsmul_comp,
    Category.assoc, chainInclusion_barycentricSubdivisionMap]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (realizeListChain_operator A σ (SimplexCategory.δ i) (subdividedStandardChain n)).symm

/-- The actual barycentric subdivision chain endomorphism for arbitrary local systems. -/
def barycentricSubdivision (A : System.{u, u} X) :
    singularChainComplex A ⟶ singularChainComplex A :=
  ChainComplex.ofHom (barycentricSubdivisionMap A) (barycentricSubdivisionMap_d A)

@[simp]
theorem barycentricSubdivision_f (A : System.{u, u} X) (n : ℕ) :
    (barycentricSubdivision A).f n = barycentricSubdivisionMap A n := rfl

end FundamentalGroupoid.LocalCoefficients
