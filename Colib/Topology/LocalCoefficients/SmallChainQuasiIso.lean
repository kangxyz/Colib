/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SmallSubdivision
public import Colib.Topology.LocalCoefficients.BarycentricIterations
public import Colib.Topology.LocalCoefficients.ChainGeneration
public import Colib.Algebra.Homology.HomologicalComplex.EventualRange

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SmallChainQuasiIso.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# The open-cover small-chain quasi-isomorphism with local coefficients

The original inclusion of cover-small chains induces isomorphisms on homology
for every open cover and every local coefficient system. The proof uses the
actual barycentric chain map, its actual homotopy on both complexes, the mesh
bound for its exact recursive affine terms, and finite additive generation of
the original coproduct chain modules.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
open scoped Simplicial

universe u v

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The actual iterates of barycentric subdivision on the original small chains. -/
def smallBarycentricSubdivisionIterate (U : ι → Set X) (A : System.{u, u} X) :
    ℕ → (smallChainComplex U A ⟶ smallChainComplex U A) :=
  Nat.rec (𝟙 _) (fun _ f ↦ smallBarycentricSubdivision U A ≫ f)

@[simp]
theorem smallBarycentricSubdivisionIterate_zero (U : ι → Set X) (A : System.{u, u} X) :
    smallBarycentricSubdivisionIterate U A 0 = 𝟙 _ := rfl

@[simp]
theorem smallBarycentricSubdivisionIterate_succ (U : ι → Set X)
    (A : System.{u, u} X) (k : ℕ) :
    smallBarycentricSubdivisionIterate U A (k + 1) =
      smallBarycentricSubdivision U A ≫ smallBarycentricSubdivisionIterate U A k := rfl

/-- Every small-chain iterate is homotopic to its actual identity. -/
def smallBarycentricSubdivisionIterateHomotopy (U : ι → Set X)
    (A : System.{u, u} X) (k : ℕ) :
    Homotopy (𝟙 (smallChainComplex U A)) (smallBarycentricSubdivisionIterate U A k) := by
  induction k with
  | zero => exact Homotopy.refl _
  | succ k ih =>
    apply (smallBarycentricSubdivisionHomotopy U A).trans
    simpa only [Category.comp_id, smallBarycentricSubdivisionIterate_succ] using
      ih.compLeft (smallBarycentricSubdivision U A)

/-- The original inclusion intertwines every actual iterate. -/
@[reassoc]
theorem smallBarycentricSubdivisionIterate_inclusion (U : ι → Set X)
    (A : System.{u, u} X) (k : ℕ) :
    smallBarycentricSubdivisionIterate U A k ≫ smallChainComplexInclusion U A =
      smallChainComplexInclusion U A ≫ barycentricSubdivisionIterate A k := by
  induction k with
  | zero => simp [smallBarycentricSubdivisionIterate]
  | succ k ih =>
    rw [smallBarycentricSubdivisionIterate_succ, barycentricSubdivisionIterate_succ,
      Category.assoc, ih, smallBarycentricSubdivision_inclusion_assoc]

/-- Each genuine finite twisted chain eventually becomes cover-small, at every
sufficiently large subdivision depth. The common depth is obtained by finite
additive generation, without any coefficient trivialization. -/
theorem exists_eventually_barycentricSubdivisionIterate_mem (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : System.{u, u} X) (n : ℕ) (x : (singularChainComplex A).X n) :
    ∃ k : ℕ, ∀ m, k ≤ m →
      (barycentricSubdivisionIterate A m).f n x ∈ smallChainSubmodule U A n := by
  let P : Submodule ℤ (chainModule A ⦋n⦌) :=
    { carrier := fun x ↦ ∃ k : ℕ, ∀ m, k ≤ m →
        (barycentricSubdivisionIterate A m).f n x ∈ smallChainSubmodule U A n
      zero_mem' := ⟨0, fun m _ ↦ by
        rw [map_zero]
        exact (smallChainSubmodule U A n).zero_mem⟩
      add_mem' := by
        rintro x y ⟨k, hk⟩ ⟨l, hl⟩
        refine ⟨max k l, fun m hm ↦ ?_⟩
        rw [map_add]
        exact (smallChainSubmodule U A n).add_mem
          (hk m ((le_max_left k l).trans hm)) (hl m ((le_max_right k l).trans hm))
      smul_mem' := by
        rintro r x ⟨k, hk⟩
        refine ⟨k, fun m hm ↦ ?_⟩
        rw [((barycentricSubdivisionIterate A m).f n).hom.map_smul]
        exact (smallChainSubmodule U A n).smul_mem r (hk m hm) }
  have hP : P = ⊤ := by
    apply chainModule_submodule_eq_top A ⦋n⦌
    intro σ a
    obtain ⟨k, hk⟩ := exists_barycentricSubdivisionIterate_simplex_mem U hU hcover A σ
    exact ⟨k, fun m hm ↦ hk m hm a⟩
  have hx : x ∈ P := by rw [hP]; trivial
  exact hx

/-- The original open-cover small-chain inclusion is a quasi-isomorphism for
arbitrary genuine local coefficient systems. No homological hypothesis is used. -/
theorem smallChainComplexInclusion_quasiIso (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : System.{u, u} X) : QuasiIso (smallChainComplexInclusion U A) := by
  apply HomologicalComplex.quasiIso_of_eventual_range (smallChainComplexInclusion U A)
    (fun n ↦ smallModuleInclusion_injective U A ⦋n⦌)
    (smallBarycentricSubdivisionIterate U A) (barycentricSubdivisionIterate A)
    (smallBarycentricSubdivisionIterate_inclusion U A)
  · intro k n
    exact (smallBarycentricSubdivisionIterateHomotopy U A k).homologyMap_eq n |>.symm.trans
      (HomologicalComplex.homologyMap_id _ n)
  · intro k n
    exact (barycentricSubdivisionIterateHomotopy A k).homologyMap_eq n |>.symm.trans
      (HomologicalComplex.homologyMap_id _ n)
  · intro n x
    obtain ⟨k, hk⟩ := exists_eventually_barycentricSubdivisionIterate_mem U hU hcover A n x
    obtain ⟨y, hy⟩ := hk k le_rfl
    exact ⟨k, y, hy⟩

/-- The induced map on actual homology is an isomorphism in every degree. -/
theorem smallChainComplexInclusion_homology_isIso (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : System.{u, u} X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallChainComplexInclusion U A) n) := by
  let := smallChainComplexInclusion_quasiIso U hU hcover A
  infer_instance

/-- The small-chain homology comparison, with its original inclusion as hom map. -/
def smallChainHomologyIso (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : System.{u, u} X) (n : ℕ) :
    (smallChainComplex U A).homology n ≅ (singularChainComplex A).homology n := by
  letI := smallChainComplexInclusion_homology_isIso U hU hcover A n
  exact asIso (HomologicalComplex.homologyMap (smallChainComplexInclusion U A) n)

@[simp]
theorem smallChainHomologyIso_hom (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : System.{u, u} X) (n : ℕ) :
    (smallChainHomologyIso U hU hcover A n).hom =
      HomologicalComplex.homologyMap (smallChainComplexInclusion U A) n := rfl

end FundamentalGroupoid.LocalCoefficients
