/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.BarycentricHomotopy
public import Colib.Analysis.Convex.StdSimplex.BarycentricTermMesh
public import Colib.Topology.LocalCoefficients.SmallChains

/-!
Adapted from `Quillen/Topology/LocalCoefficients/BarycentricIterations.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Actual iterated subdivision and its geometric support

Repeated subdivision is a concrete chain map. Its terms are compositions of
the actual descending-face affine maps controlled by the mesh theorem. The
support theorem below is proved for the original local coefficients, including
all coefficient transports between successive new first vertices.
-/

@[expose] public section

open stdSimplex.BarycentricSubdivision


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open FreeAbelianGroup stdSimplex
open CategoryTheory Limits
open scoped Simplicial

universe u v

namespace FundamentalGroupoid.LocalCoefficients

open stdSimplex.BarycentricSubdivision

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The actual `k`-fold subdivision chain map, with order of composition explicit. -/
def barycentricSubdivisionIterate (A : System.{u, u} X) (k : ℕ) :
    singularChainComplex A ⟶ singularChainComplex A :=
  match k with
  | 0 => 𝟙 _
  | k + 1 => barycentricSubdivision A ≫ barycentricSubdivisionIterate A k

@[simp]
theorem barycentricSubdivisionIterate_zero (A : System.{u, u} X) :
    barycentricSubdivisionIterate A 0 = 𝟙 _ := rfl

@[simp]
theorem barycentricSubdivisionIterate_succ (A : System.{u, u} X) (k : ℕ) :
    barycentricSubdivisionIterate A (k + 1) =
      barycentricSubdivision A ≫ barycentricSubdivisionIterate A k := rfl

/-- Every iterate is homotopic to the original identity chain map. -/
def barycentricSubdivisionIterateHomotopy (A : System.{u, u} X) (k : ℕ) :
    Homotopy (𝟙 (singularChainComplex A)) (barycentricSubdivisionIterate A k) := by
  induction k with
  | zero => exact Homotopy.refl _
  | succ k ih =>
    apply (barycentricSubdivisionHomotopy A).trans
    simpa only [Category.comp_id, barycentricSubdivisionIterate_succ] using
      ih.compLeft (barycentricSubdivision A)

/-- A support condition on realized generators extends to every finite integral
combination, even after postcomposition by a specified linear map. -/
theorem realizeListChain_comp_mem (A : System.{u, u} X) {N n : ℕ}
    (σ : SingularSimplex X ⦋N⦌) (x : _root_.stdSimplex ℝ (Fin (N + 1)))
    {D : ModuleCat.{u} ℤ} (f : chainModule A ⦋n⦌ ⟶ D) (Q : Submodule ℤ D)
    (P : List (_root_.stdSimplex ℝ (Fin (N + 1))) → Prop)
    (h : ∀ l, P l → ∀ a : fiber A (σ x), (affineListTerm A σ x n l ≫ f) a ∈ Q)
    (c : OrientedList.Chain (_root_.stdSimplex ℝ (Fin (N + 1))))
    (hc : OrientedList.Supported P c) (a : fiber A (σ x)) :
    (realizeListChain A σ x n c ≫ f) a ∈ Q := by
  induction hc with
  | zero => simp
  | generator l hl => simpa only [realizeListChain_generator] using h l hl a
  | add hc hd ihc ihd =>
    rw [map_add, Preadditive.add_comp]
    exact Q.add_mem ihc ihd
  | neg hc ihc =>
    rw [map_neg, Preadditive.neg_comp]
    exact Q.neg_mem ihc

/-- Each exact recursive list term realizes as its mesh-controlled affine map. -/
theorem affineListTerm_subdivisionTerm (A : System.{u, u} X) {n : ℕ}
    (σ : SingularSimplex X ⦋n⦌) (x : _root_.stdSimplex ℝ (Fin (n + 1)))
    (t : SubdivisionSimplex n) :
    affineListTerm A σ x n t.val = transportedSimplexTerm A σ x (subdivisionTermMap t) := by
  have hl : t.val.length = n + 1 := by
    simpa only [standardVertices, List.length_ofFn] using t.property.length
  rw [affineListTerm_of_length A σ x t.val hl]
  rfl

/-- Every coefficient on a small simplex belongs to the original small submodule. -/
theorem chainInclusion_mem_smallChainSubmodule (U : ι → Set X) (A : System.{u, u} X)
    {n : ℕ} (σ : SingularSimplex X ⦋n⦌) (hσ : IsCoverSmall U σ) (a : simplexFiber A σ) :
    chainInclusion A σ a ∈ smallChainSubmodule U A n := by
  refine ⟨smallChainInclusion U A ⟨σ, hσ⟩ a, ?_⟩
  exact ConcreteCategory.congr_hom
    (smallChainInclusion_smallModuleInclusion U A ⟨σ, hσ⟩) a

/-- If every actual depth-`k` geometric term is cover-small, the actual `k`-fold
subdivision of every coefficient on the original simplex is a small chain. -/
theorem barycentricSubdivisionIterate_simplex_mem (U : ι → Set X)
    (A : System.{u, u} X) {n : ℕ} (k : ℕ) (σ : SingularSimplex X ⦋n⦌)
    (hσ : ∀ ps : List (SubdivisionSimplex n), ps.length = k →
      IsCoverSmall U (σ.comp (iteratedTermMap ps))) (a : simplexFiber A σ) :
    (chainInclusion A σ ≫ (barycentricSubdivisionIterate A k).f n) a ∈
      smallChainSubmodule U A n := by
  induction k generalizing σ with
  | zero =>
    have hsmall := hσ [] rfl
    rw [iteratedTermMap, ContinuousMap.comp_id] at hsmall
    simpa only [barycentricSubdivisionIterate_zero, HomologicalComplex.id_f,
      Category.comp_id, singularChainComplex,
      AlgebraicTopology.alternatingFaceMapComplex_obj_X, simplicialModule] using
      chainInclusion_mem_smallChainSubmodule U A σ hsmall a
  | succ k ih =>
    rw [barycentricSubdivisionIterate_succ, HomologicalComplex.comp_f,
      barycentricSubdivision_f, ← Category.assoc, chainInclusion_barycentricSubdivisionMap]
    apply realizeListChain_comp_mem A σ (stdSimplex.vertex 0)
      ((barycentricSubdivisionIterate A k).f n) (smallChainSubmodule U A n)
      (OrientedList.SubdivisionTerm listBarycenter (standardVertexList n))
      ?_ _ (OrientedList.subdivision_supported_terms
        listBarycenter (standardVertexList n)) a
    intro l hl b
    let t : SubdivisionSimplex n := ⟨l, hl⟩
    rw [affineListTerm_subdivisionTerm A σ (stdSimplex.vertex 0) t]
    unfold transportedSimplexTerm
    rw [Category.assoc, ModuleCat.comp_apply]
    apply ih (σ.comp (subdivisionTermMap t))
    intro ps hps
    have hh := hσ (t :: ps) (by simp only [List.length_cons, hps])
    exact hh

/-- Every original simplex, with all its original coefficients, eventually becomes
small under the actually constructed subdivision operator, at every larger depth. -/
theorem exists_barycentricSubdivisionIterate_simplex_mem (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : System.{u, u} X) {n : ℕ} (σ : SingularSimplex X ⦋n⦌) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m → ∀ a : simplexFiber A σ,
      (chainInclusion A σ ≫ (barycentricSubdivisionIterate A m).f n) a ∈
        smallChainSubmodule U A n := by
  obtain ⟨k, hk⟩ := exists_eventually_iteratedTermMap_cover_small σ U hU hcover
  refine ⟨k, fun m hm a ↦ barycentricSubdivisionIterate_simplex_mem U A m σ ?_ a⟩
  intro ps hps
  exact hk ps (hps.symm ▸ hm)

/-- A finite family has one common eventual-small subdivision depth, uniformly
for every coefficient in every original fiber and for all larger depths. -/
theorem exists_uniform_barycentricSubdivisionIterate_simplex_mem
    {κ : Type*} [Finite κ] (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : System.{u, u} X) {n : ℕ} (σ : κ → SingularSimplex X ⦋n⦌) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m → ∀ s : κ, ∀ a : simplexFiber A (σ s),
      (chainInclusion A (σ s) ≫ (barycentricSubdivisionIterate A m).f n) a ∈
        smallChainSubmodule U A n := by
  obtain ⟨k, hk⟩ := exists_uniform_iteratedTermMap_cover_small σ U hU hcover
  refine ⟨k, fun m hm s a ↦ barycentricSubdivisionIterate_simplex_mem U A m (σ s) ?_ a⟩
  intro ps hps
  exact hk s ps (hps.symm ▸ hm)

end FundamentalGroupoid.LocalCoefficients
