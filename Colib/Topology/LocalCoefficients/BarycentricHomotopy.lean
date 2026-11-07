/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.BarycentricChains
public import Mathlib.Algebra.Homology.Homotopy

/-!
Adapted from `Quillen/Topology/LocalCoefficients/BarycentricHomotopy.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# The explicit twisted homotopy from identity to barycentric subdivision

The recursively coned affine-list homotopy is realized inside each original
singular simplex with its original coefficient transport. The resulting
identity is proved for the actual twisted differential, in every degree.
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

/-- The coning homotopy is natural under actual simplicial operators. -/
theorem homotopyListChain_operator {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (c : OrientedList.Chain (StdSimplex ℝ (Fin (m + 1)))) :
    OrientedList.mapPoints (simplexOperatorMap α)
        (OrientedList.homotopy listBarycenter c) =
      OrientedList.homotopy listBarycenter
        (OrientedList.mapPoints (simplexOperatorMap α) c) := by
  apply OrientedList.mapPoints_homotopy
  intro l hl
  have h := listBarycenter_natural l hl
    (fun i ↦ (StdSimplex.single (α i) : StdSimplex ℝ (Fin (n + 1))))
  rw [affineSimplex_operator] at h
  exact h.symm

/-- The explicit homotopy chain associated with the original parameter simplex. -/
def standardHomotopyChain (n : ℕ) :
    OrientedList.Chain (StdSimplex ℝ (Fin (n + 1))) :=
  OrientedList.homotopy listBarycenter (standardVertexChain n)

/-- The homotopy raises dimension by one. -/
theorem standardHomotopyChain_homogeneous (n : ℕ) :
    OrientedList.Homogeneous (n + 2) (standardHomotopyChain n) := by
  apply OrientedList.Homogeneous.homotopy
  exact OrientedList.Supported.generator _ (standardVertexList_length n)

/-- The homotopy relation on an original positive-dimensional parameter simplex. -/
theorem standardHomotopyChain_boundary (n : ℕ) :
    OrientedList.boundary (standardHomotopyChain (n + 1)) +
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          OrientedList.mapPoints (simplexOperatorMap (SimplexCategory.δ i))
            (standardHomotopyChain n) =
      standardVertexChain (n + 1) - subdividedStandardChain (n + 1) := by
  have h := OrientedList.boundary_homotopy_add_homotopy_boundary
    listBarycenter (standardVertexChain (n + 1))
  rw [standardVertexChain_boundary] at h
  simpa only [map_sum, map_zsmul, ← homotopyListChain_operator,
    standardHomotopyChain, subdividedStandardChain] using h

/-- The augmentation term contributes zero to the degree-zero homotopy relation. -/
theorem standardHomotopyChain_boundary_zero :
    OrientedList.boundary (standardHomotopyChain 0) =
      standardVertexChain 0 - subdividedStandardChain 0 := by
  have h := OrientedList.boundary_homotopy_add_homotopy_boundary
    listBarycenter (standardVertexChain 0)
  have hz : OrientedList.homotopy listBarycenter
      (OrientedList.boundary (standardVertexChain 0)) = 0 := by
    simp [standardVertexChain, standardVertexList, List.ofFn_succ]
  simpa only [hz, add_zero, standardHomotopyChain, subdividedStandardChain] using h

/-- The original affine list realizes as exactly the original simplex summand. -/
theorem realizeListChain_standard (A : System.{u, u} X) {n : ℕ}
    (σ : SingularSimplex X ⦋n⦌) :
    realizeListChain A σ (StdSimplex.single 0) n (standardVertexChain n) =
      chainInclusion A σ := by
  rw [standardVertexChain, realizeListChain_generator,
    affineListTerm_of_length A σ (StdSimplex.single 0) _ (standardVertexList_length n)]
  unfold standardVertexList
  rw [listVertices_ofFn, affineSimplex_identity]
  simp only [transportedSimplexTerm, ContinuousMap.id_apply, simplexTransport_self,
    Category.id_comp]
  simpa only [eqToHom_refl, Category.id_comp] using
    (chainInclusion_congr A (ContinuousMap.comp_id σ)).symm

/-- The concrete degree-raising local-coefficient homotopy operator. -/
def barycentricHomotopyMap (A : System.{u, u} X) (n : ℕ) :
    (singularChainComplex A).X n ⟶ (singularChainComplex A).X (n + 1) :=
  Sigma.desc fun σ ↦ realizeListChain A σ (StdSimplex.single 0) (n + 1)
    (standardHomotopyChain n)

@[reassoc (attr := simp)]
theorem chainInclusion_barycentricHomotopyMap (A : System.{u, u} X) (n : ℕ)
    (σ : SingularSimplex X ⦋n⦌) :
    chainInclusion A σ ≫ barycentricHomotopyMap A n =
      realizeListChain A σ (StdSimplex.single 0) (n + 1) (standardHomotopyChain n) :=
  Sigma.ι_comp_desc _ _

/-- The degree-zero homotopy equation retains the original twisted differential. -/
theorem barycentricHomotopyMap_d_zero (A : System.{u, u} X) :
    barycentricHomotopyMap A 0 ≫ (singularChainComplex A).d 1 0 =
      𝟙 (chainModule A ⦋0⦌) - barycentricSubdivisionMap A 0 := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion A σ ≫ (_ ≫ _) = chainInclusion A σ ≫ (_ - _)
  rw [chainInclusion_barycentricHomotopyMap_assoc,
    realizeListChain_boundary A σ (StdSimplex.single 0) _
      (standardHomotopyChain_homogeneous 0), standardHomotopyChain_boundary_zero,
    map_sub, realizeListChain_standard]
  simp

/-- The full homotopy equation in every positive degree. -/
theorem barycentricHomotopyMap_d (A : System.{u, u} X) (n : ℕ) :
    barycentricHomotopyMap A (n + 1) ≫ (singularChainComplex A).d (n + 2) (n + 1) +
        (singularChainComplex A).d (n + 1) n ≫ barycentricHomotopyMap A n =
      𝟙 (chainModule A ⦋n + 1⦌) - barycentricSubdivisionMap A (n + 1) := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion A σ ≫ (_ + _) = chainInclusion A σ ≫ (_ - _)
  rw [Preadditive.comp_add, chainInclusion_barycentricHomotopyMap_assoc,
    realizeListChain_boundary A σ (StdSimplex.single 0) _
      (standardHomotopyChain_homogeneous (n + 1)), chainInclusion_d_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
    chainInclusion_barycentricHomotopyMap]
  have hsum :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (restrictionTransport A σ (SimplexCategory.δ i) ≫
          realizeListChain A (restrictSimplex σ (SimplexCategory.δ i))
            (StdSimplex.single 0) (n + 1) (standardHomotopyChain n))) =
      realizeListChain A σ (StdSimplex.single 0) (n + 1)
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          OrientedList.mapPoints (simplexOperatorMap (SimplexCategory.δ i))
            (standardHomotopyChain n)) := by
    simp only [map_sum, map_zsmul, realizeListChain_operator]
  rw [hsum]
  change realizeListChain A σ (StdSimplex.single 0) (n + 1) _ +
    realizeListChain A σ (StdSimplex.single 0) (n + 1) _ = _
  rw [← (realizeListChain A σ (StdSimplex.single 0) (n + 1)).map_add,
    standardHomotopyChain_boundary, map_sub, realizeListChain_standard]
  simp

/-- The degree-raising components, indexed by the chain-complex shape. -/
def barycentricHomotopyData (A : System.{u, u} X) (i j : ℕ)
    (h : (ComplexShape.down ℕ).Rel j i) :
    (singularChainComplex A).X i ⟶ (singularChainComplex A).X j := by
  simp only [ComplexShape.down_Rel] at h
  subst j
  exact barycentricHomotopyMap A i

/-- The explicit degreewise equations identify the associated null-homotopic map. -/
theorem barycentricHomotopyData_nullHomotopicMap (A : System.{u, u} X) :
    Homotopy.nullHomotopicMap' (barycentricHomotopyData A) =
      𝟙 (singularChainComplex A) - barycentricSubdivision A := by
  ext n : 1
  cases n with
  | zero =>
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (k₁ := 1) rfl
      (fun l ↦ by simp only [ComplexShape.down_Rel]; omega)]
    simpa only [barycentricHomotopyData, HomologicalComplex.sub_f_apply,
      HomologicalComplex.id_f, barycentricSubdivision_f, singularChainComplex,
      AlgebraicTopology.alternatingFaceMapComplex_obj_X, simplicialModule] using
      barycentricHomotopyMap_d_zero A
  | succ n =>
    rw [Homotopy.nullHomotopicMap'_f (k₂ := n + 2) (k₀ := n) rfl rfl]
    simpa only [barycentricHomotopyData, HomologicalComplex.sub_f_apply,
      HomologicalComplex.id_f, barycentricSubdivision_f, add_comm, singularChainComplex,
      AlgebraicTopology.alternatingFaceMapComplex_obj_X, simplicialModule] using
      barycentricHomotopyMap_d A n

/-- The actual barycentric subdivision endomorphism is chain homotopic to identity. -/
def barycentricSubdivisionHomotopy (A : System.{u, u} X) :
    Homotopy (𝟙 (singularChainComplex A)) (barycentricSubdivision A) := by
  refine Homotopy.equivSubZero.symm ?_
  rw [← barycentricHomotopyData_nullHomotopicMap]
  exact Homotopy.nullHomotopy' (barycentricHomotopyData A)

end FundamentalGroupoid.LocalCoefficients
