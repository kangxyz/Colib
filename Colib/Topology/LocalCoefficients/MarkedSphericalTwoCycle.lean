/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.NormalizedCapValue
public import Colib.Topology.LocalCoefficients.IntegralChainEvaluation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The marked original absolute spherical two-cycle

In the actual unnormalized integral singular complex, a spherical triangle
has the same boundary as the constant triangle. Their difference is therefore
an actual absolute cycle. Its original cap evaluation is the specified original
Pi-two class; the constant triangle has value zero by the normalized constant cap.
-/

/-! Implementation source: `Quillen/Topology/LocalCoefficients/MarkedSphericalTwoCycle.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native singular chains,
ordered cap evaluation and original connecting homomorphism are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Topology stdSimplex
open scoped Simplicial
universe u

namespace FundamentalGroupoid.LocalCoefficients
variable {Y : Type u} [TopologicalSpace Y] {y : Y}

/-- Every genuine boundary face of a spherical native simplex is constant. -/
theorem spherical_restrictSimplex_eq_const {n : ℕ}
    (f₀ : SphericalSimplex Y y (n + 1)) (i : Fin (n + 2)) :
    restrictSimplex f₀.val (SimplexCategory.δ i) = ContinuousMap.const _ y := by
  ext x
  change f₀ (stdSimplex.map i.succAbove x) = y
  apply f₀.boundary
  refine ⟨i, ?_⟩
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove x) i = 0
  simp [FunOnFinite.linearMap_apply_apply]

/-- The two original generators have equal actual singular boundaries. -/
theorem sphericalTriangle_chain_boundary (a : SphericalSimplex Y y 2) :
    chainInclusion (constant Y integralCoefficients.{u}) a.val ≫
      (singularChainComplex (constant Y integralCoefficients.{u})).d 2 1 =
    chainInclusion (constant Y integralCoefficients.{u}) (ContinuousMap.const _ y) ≫
      (singularChainComplex (constant Y integralCoefficients.{u})).d 2 1 := by
  rw [chainInclusion_d, chainInclusion_d]
  apply Finset.sum_congr rfl
  intro i _
  rw [spherical_restrictSimplex_eq_const a i]
  rfl

/-- The actual absolute chain is the spherical generator minus the constant generator. -/
def sphericalTwoChain (a : SphericalSimplex Y y 2) :
    (singularChainComplex (constant Y integralCoefficients.{u})).X 2 :=
  chainInclusion (constant Y integralCoefficients.{u}) a.val (ULift.up 1) -
    chainInclusion (constant Y integralCoefficients.{u})
      (ContinuousMap.const _ y) (ULift.up 1)

/-- The displayed chain is an actual absolute cycle in the unnormalized singular complex. -/
theorem sphericalTwoChain_cycle (a : SphericalSimplex Y y 2) :
    (singularChainComplex (constant Y integralCoefficients.{u})).d 2 1
      (sphericalTwoChain a) = 0 := by
  rw [sphericalTwoChain, map_sub]
  exact sub_eq_zero.mpr (ConcreteCategory.congr_hom (sphericalTriangle_chain_boundary a)
    (ULift.up 1))

/-- The marked chain as an element of the original categorical cycle object. -/
def sphericalTwoCycle (a : SphericalSimplex Y y 2) :
    (singularChainComplex (constant Y integralCoefficients.{u})).cycles 2 := by
  refine ((singularChainComplex (constant Y integralCoefficients.{u})).sc 2).cyclesMk
    (sphericalTwoChain a) ?_
  change (singularChainComplex (constant Y integralCoefficients.{u})).d 2
    ((ComplexShape.down ℕ).next 2) (sphericalTwoChain a) = 0
  rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
  exact sphericalTwoChain_cycle a

/-- Taking the underlying chain returns the original marked difference. -/
theorem iCycles_sphericalTwoCycle (a : SphericalSimplex Y y 2) :
    (singularChainComplex (constant Y integralCoefficients.{u})).iCycles 2
      (sphericalTwoCycle a) = sphericalTwoChain a :=
  ((singularChainComplex (constant Y integralCoefficients.{u})).sc 2).i_cyclesMk _ _

variable [SimplyConnectedSpace Y]

/-- Extend the actual based-triangle cap value by zero on nonbased singular triangles. -/
def integralTwoCapValue (y : Y) (τ : SingularSimplex Y ⦋2⦌) :
    Additive (HomotopyGroup.Pi 2 Y y) := by
  classical
  exact if hτ : ∀ i, τ (stdSimplex.vertex i) = y then
    HomotopyFiber.basedTriangleValue y τ hτ else 0

/-- A based original triangle retains its actual cap value. -/
theorem integralTwoCapValue_based (y : Y) (τ : SingularSimplex Y ⦋2⦌)
    (hτ : ∀ i, τ (stdSimplex.vertex i) = y) :
    integralTwoCapValue y τ = HomotopyFiber.basedTriangleValue y τ hτ := by
  simp only [integralTwoCapValue, dite_eq_left hτ]

/-- The actual spherical generator evaluates to the specified original homotopy class. -/
theorem integralTwoCapValue_spherical (a : SphericalSimplex Y y 2) :
    integralTwoCapValue y a.val = Additive.ofMul a.homotopyClassStick := by
  rw [integralTwoCapValue_based y a.val (HomotopyFiber.sphericalTriangle_vertex a)]
  exact HomotopyFiber.basedTriangleValue_spherical y a

/-- The constant singular triangle has zero cap value. -/
theorem integralTwoCapValue_const (y : Y) :
    integralTwoCapValue y (ContinuousMap.const _ y) = 0 := by
  rw [integralTwoCapValue_based y _ (fun _ ↦ rfl)]
  exact HomotopyFiber.basedTriangleValue_const y

/-- The original coproduct evaluation of the marked absolute cycle is the original Pi-two class. -/
theorem sphericalTwoChain_cap_evaluation (a : SphericalSimplex Y y 2) :
    integralChainEvaluation 2 (integralTwoCapValue y) (sphericalTwoChain a) =
      Additive.ofMul a.homotopyClassStick := by
  rw [sphericalTwoChain, map_sub, integralChainEvaluation_inclusion,
    integralChainEvaluation_inclusion, integralTwoCapValue_spherical, integralTwoCapValue_const]
  simp only [one_smul, smul_zero, sub_zero]

/-- Evaluation annihilates the actual differential of each based ambient tetrahedron. -/
theorem integralTwoCapValue_tetrahedron_boundary
    (T : SingularSimplex Y ⦋3⦌) (hT : ∀ i, T (stdSimplex.vertex i) = y)
    (b : ULift.{u} ℤ) :
    integralChainEvaluation 2 (integralTwoCapValue y)
      ((singularChainComplex (constant Y integralCoefficients.{u})).d 3 2
        (chainInclusion (constant Y integralCoefficients.{u}) T b)) = 0 := by
  rw [integralChainEvaluation_boundary]
  have he (i : Fin 4) :
      integralTwoCapValue y (restrictSimplex T (SimplexCategory.δ i)) =
        HomotopyFiber.basedTriangleValue y (HomotopyFiber.sourceTetrahedronFace T i)
          (HomotopyFiber.sourceTetrahedronFace_vertex T hT i) :=
    integralTwoCapValue_based y _ (HomotopyFiber.sourceTetrahedronFace_vertex T hT i)
  simp only [he]
  calc
    _ = b.down • (HomotopyFiber.basedTriangleValue y
        (HomotopyFiber.sourceTetrahedronFace T 0)
        (HomotopyFiber.sourceTetrahedronFace_vertex T hT 0) -
      HomotopyFiber.basedTriangleValue y (HomotopyFiber.sourceTetrahedronFace T 1)
        (HomotopyFiber.sourceTetrahedronFace_vertex T hT 1) +
      HomotopyFiber.basedTriangleValue y (HomotopyFiber.sourceTetrahedronFace T 2)
        (HomotopyFiber.sourceTetrahedronFace_vertex T hT 2) -
      HomotopyFiber.basedTriangleValue y (HomotopyFiber.sourceTetrahedronFace T 3)
        (HomotopyFiber.sourceTetrahedronFace_vertex T hT 3)) := by
          simp [Fin.sum_univ_succ, sub_eq_add_neg, smul_add, smul_neg, add_assoc]
    _ = 0 := by rw [HomotopyFiber.basedTriangleValue_tetrahedral y T hT, smul_zero]

end FundamentalGroupoid.LocalCoefficients
