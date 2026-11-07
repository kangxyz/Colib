/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.BarycentricSubdivision

public import Colib.Topology.LocalCoefficients.HomotopyEquivalence

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SimplexProductCoefficients.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Local coefficients on a product with a geometric simplex

The affine contraction to a specified vertex identifies every local system on
`X × Δ[n]` with the pullback of its restriction to that vertex slice. Its component
is the actual radial-path transport, rather than an unspecified equivalence.
Choosing vertex zero gives the coefficient identification used by the original
first-vertex convention in simplicial replacement.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped unitInterval Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable (X : Type u) [TopologicalSpace X]

/-- The original projection from a product with the geometric `n`-simplex. -/
def simplexProductProjection (n : ℕ) : C(X × _root_.stdSimplex ℝ (Fin (n + 1)), X) :=
  ⟨Prod.fst, continuous_fst⟩

/-- The original inclusion of a prescribed vertex slice. -/
def simplexProductVertex (n : ℕ) (v : Fin (n + 1)) :
    C(X, X × _root_.stdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun x ↦ (x, _root_.stdSimplex.vertex v), by fun_prop⟩

/-- The specified affine contraction starts at the vertex slice and ends at the identity. -/
def simplexProductVertexHomotopy (n : ℕ) (v : Fin (n + 1)) :
    ((simplexProductVertex X n v).comp (simplexProductProjection X n)).Homotopy
      (ContinuousMap.id _) where
  toFun z := (z.2.1,
    stdSimplex.BarycentricSubdivision.affineSimplex ![stdSimplex.vertex v, z.2.2]
      (stdSimplexHomeomorphUnitInterval.symm z.1))
  continuous_toFun := by
    apply Continuous.prodMk continuous_snd.fst
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    simp only [Fin.sum_univ_two]
    change Continuous (fun z : unitInterval × (X × _root_.stdSimplex ℝ (Fin (n + 1))) ↦
      (1 - (z.1 : ℝ)) * (stdSimplex.vertex v : _root_.stdSimplex ℝ (Fin (n + 1))) i +
        (z.1 : ℝ) * z.2.2.val i)
    have ht : Continuous (fun z : unitInterval ×
        (X × _root_.stdSimplex ℝ (Fin (n + 1))) ↦ (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hz : Continuous (fun z : unitInterval ×
        (X × _root_.stdSimplex ℝ (Fin (n + 1))) ↦ z.2.2.val i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd.snd)
    exact ((continuous_const.sub ht).mul_const
      ((stdSimplex.vertex v : _root_.stdSimplex ℝ (Fin (n + 1))) i)).add (ht.mul hz)
  map_zero_left z := by
    refine Prod.ext ?_ ?_
    · rfl
    ext i
    simp only [stdSimplex.BarycentricSubdivision.affineSimplex_weights, Fin.sum_univ_two]
    change (1 - (0 : ℝ)) * (stdSimplex.vertex v : _root_.stdSimplex ℝ (Fin (n + 1))) i +
      (0 : ℝ) * z.2 i = _
    simp [simplexProductVertex, simplexProductProjection]
  map_one_left z := by
    refine Prod.ext ?_ ?_
    · rfl
    ext i
    simp only [stdSimplex.BarycentricSubdivision.affineSimplex_weights, Fin.sum_univ_two]
    change (1 - (1 : ℝ)) * (stdSimplex.vertex v : _root_.stdSimplex ℝ (Fin (n + 1))) i +
      (1 : ℝ) * z.2 i = _
    simp

/-- The product projection is a homotopy equivalence with the original vertex section. -/
def simplexProductProjectionEquiv (n : ℕ) (v : Fin (n + 1)) :
    ContinuousMap.HomotopyEquiv (X × _root_.stdSimplex ℝ (Fin (n + 1))) X where
  toFun := simplexProductProjection X n
  invFun := simplexProductVertex X n v
  left_inv := ⟨simplexProductVertexHomotopy X n v⟩
  right_inv := by
    have h : (simplexProductProjection X n).comp (simplexProductVertex X n v) =
        ContinuousMap.id X := rfl
    rw [h]

/-- Radial transport trivializes every local system in the simplex direction. -/
def simplexProductVertexCoefficients (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × _root_.stdSimplex ℝ (Fin (n + 1)))) :
    pullback (simplexProductProjection X n) (pullback (simplexProductVertex X n v) A) ≅ A :=
  (pullbackCompositionIso (simplexProductProjection X n) (simplexProductVertex X n v) A).symm ≪≫
    homotopyPullbackIso (simplexProductVertexHomotopy X n v) A ≪≫ pullbackIdentityIso A

/-- The coefficient identification is exactly transport along the specified radial path. -/
@[simp]
theorem simplexProductVertexCoefficients_hom_app (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × _root_.stdSimplex ℝ (Fin (n + 1))))
    (z : X × _root_.stdSimplex ℝ (Fin (n + 1))) :
    (simplexProductVertexCoefficients X n v A).hom.app (FundamentalGroupoid.mk z) =
      transport A ((simplexProductVertexHomotopy X n v).evalAt z) := by
  simp [simplexProductVertexCoefficients, pullbackCompositionIso, pullbackIdentityIso]

/-- The original projection induces an isomorphism for every target local system. -/
theorem simplexProductProjection_homology_isIso (n : ℕ) (A : System.{u, u} X) (k : ℕ) :
    IsIso (pushforwardHomologyMap (simplexProductProjection X n) A k) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv (simplexProductProjectionEquiv X n 0) A k

/-- The original vertex section induces an isomorphism for every local system on the product. -/
theorem simplexProductVertex_homology_isIso (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × _root_.stdSimplex ℝ (Fin (n + 1)))) (k : ℕ) :
    IsIso (pushforwardHomologyMap (simplexProductVertex X n v) A k) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv (simplexProductProjectionEquiv X n v).symm A k

end FundamentalGroupoid.LocalCoefficients
