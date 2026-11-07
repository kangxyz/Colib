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

open Convexity
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
def simplexProductProjection (n : ℕ) : C(X × StdSimplex ℝ (Fin (n + 1)), X) :=
  ⟨Prod.fst, continuous_fst⟩

/-- The original inclusion of a prescribed vertex slice. -/
def simplexProductVertex (n : ℕ) (v : Fin (n + 1)) :
    C(X, X × StdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun x ↦ (x, StdSimplex.single v), by fun_prop⟩

/-- The specified affine contraction starts at the vertex slice and ends at the identity. -/
def simplexProductVertexHomotopy (n : ℕ) (v : Fin (n + 1)) :
    ((simplexProductVertex X n v).comp (simplexProductProjection X n)).Homotopy
      (ContinuousMap.id _) where
  toFun z := (z.2.1,
    StdSimplex.BarycentricSubdivision.affineSimplex ![StdSimplex.single v, z.2.2]
      (StdSimplex.homeomorphI.symm z.1))
  continuous_toFun := by
    have h₁ (t : unitInterval) : (StdSimplex.homeomorphI.symm t).weights 1 = (t : ℝ) := by
      simpa only [StdSimplex.homeomorphI_apply_coe] using
        congrArg Subtype.val (StdSimplex.homeomorphI.apply_symm_apply t)
    have h₀ (t : unitInterval) : (StdSimplex.homeomorphI.symm t).weights 0 = 1 - (t : ℝ) := by
      have ht := StdSimplex.total_fin_two (StdSimplex.homeomorphI.symm t)
      rw [h₁] at ht
      exact eq_sub_of_add_eq ht
    apply Continuous.prodMk continuous_snd.fst
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
    apply continuous_pi
    intro i
    simp only [Function.comp_apply,
      StdSimplex.BarycentricSubdivision.affineSimplex_weights, Fin.sum_univ_two]
    change Continuous (fun z : unitInterval × (X × StdSimplex ℝ (Fin (n + 1))) ↦
      (StdSimplex.homeomorphI.symm z.1).weights 0 *
          (StdSimplex.single v : StdSimplex ℝ (Fin (n + 1))).weights i +
        (StdSimplex.homeomorphI.symm z.1).weights 1 * z.2.2.weights i)
    simp_rw [h₀, h₁]
    fun_prop
  map_zero_left z := by
    simp [simplexProductVertex, simplexProductProjection]
  map_one_left z := by
    simp

/-- The product projection is a homotopy equivalence with the original vertex section. -/
def simplexProductProjectionEquiv (n : ℕ) (v : Fin (n + 1)) :
    ContinuousMap.HomotopyEquiv (X × StdSimplex ℝ (Fin (n + 1))) X where
  toFun := simplexProductProjection X n
  invFun := simplexProductVertex X n v
  left_inv := ⟨simplexProductVertexHomotopy X n v⟩
  right_inv := by
    have h : (simplexProductProjection X n).comp (simplexProductVertex X n v) =
        ContinuousMap.id X := rfl
    rw [h]

/-- Radial transport trivializes every local system in the simplex direction. -/
def simplexProductVertexCoefficients (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1)))) :
    pullback (simplexProductProjection X n) (pullback (simplexProductVertex X n v) A) ≅ A :=
  (pullbackCompositionIso (simplexProductProjection X n) (simplexProductVertex X n v) A).symm ≪≫
    homotopyPullbackIso (simplexProductVertexHomotopy X n v) A ≪≫ pullbackIdentityIso A

/-- The coefficient identification is exactly transport along the specified radial path. -/
@[simp]
theorem simplexProductVertexCoefficients_hom_app (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1))))
    (z : X × StdSimplex ℝ (Fin (n + 1))) :
    (simplexProductVertexCoefficients X n v A).hom.app (FundamentalGroupoid.mk z) =
      transport A ((simplexProductVertexHomotopy X n v).evalAt z) := by
  simp [simplexProductVertexCoefficients, pullbackCompositionIso, pullbackIdentityIso]

/-- The original projection induces an isomorphism for every target local system. -/
theorem simplexProductProjection_homology_isIso (n : ℕ) (A : System.{u, u} X) (k : ℕ) :
    IsIso (pushforwardHomologyMap (simplexProductProjection X n) A k) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv (simplexProductProjectionEquiv X n 0) A k

/-- The original vertex section induces an isomorphism for every local system on the product. -/
theorem simplexProductVertex_homology_isIso (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1)))) (k : ℕ) :
    IsIso (pushforwardHomologyMap (simplexProductVertex X n v) A k) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv (simplexProductProjectionEquiv X n v).symm A k

end FundamentalGroupoid.LocalCoefficients
