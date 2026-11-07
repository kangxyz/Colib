/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.MarkedSphericalTwoCycle
public import Colib.Topology.Realization.JointFiniteVertexStraightening

/-!
# Cap evaluation of actual finite straightening endpoints

The assignments are extended by zero outside the specified finite families and
then by the actual integral coproduct universal property. Face compatibility is
proved only where needed on the original finite support. Original target
tetrahedron boundaries evaluate to zero; no global chain-map assertion about
the zero extension is made.
-/

/-! Implementation source: `Quillen/Topology/LocalCoefficients/FiniteCapEvaluation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native singular chains,
ordered cap evaluation and original connecting homomorphism are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Topology stdSimplex
open scoped Simplicial Topology
universe u

namespace FundamentalGroupoid.LocalCoefficients
variable {Y : Type u} [TopologicalSpace Y] {y : Y}
variable {S F : FiniteSimplexFamily Y} {hS : S.FaceClosed} {N : ℕ}
variable [SimplyConnectedSpace Y]

/-- The actual endpoint cap value, extended by zero off the selected original finite family. -/
def finiteTwoCapValue (P : PartialSimplexStraightening 1 y S F hS N)
    (τ : SingularSimplex Y ⦋2⦌) : Additive (HomotopyGroup.Pi 2 Y y) := by
  classical
  exact if hτ : τ ∈ S 2 then integralTwoCapValue y (P.endpoint 2 ⟨τ, hτ⟩) else 0

/-- On a selected original triangle, evaluation retains its constructed based endpoint. -/
theorem finiteTwoCapValue_selected (P : PartialSimplexStraightening 1 y S F hS N)
    (hN : 2 < N) (τ : SingularSimplex Y ⦋2⦌) (hτ : τ ∈ S 2) :
    finiteTwoCapValue P τ = HomotopyFiber.basedTriangleValue y (P.endpoint 2 ⟨τ, hτ⟩)
      (P.endpoint_vertices 2 hN ⟨τ, hτ⟩) := by
  classical
  rw [finiteTwoCapValue, dite_eq_left hτ]
  exact integralTwoCapValue_based y _ (P.endpoint_vertices 2 hN ⟨τ, hτ⟩)

/-- A fixed original triangle keeps exactly its original value. -/
theorem finiteTwoCapValue_fixed (P : PartialSimplexStraightening 1 y S F hS N)
    (τ : SingularSimplex Y ⦋2⦌) (hτ : τ ∈ S 2) (hF : τ ∈ F 2) :
    finiteTwoCapValue P τ = integralTwoCapValue y τ := by
  classical
  rw [finiteTwoCapValue, dite_eq_left hτ, P.endpoint_fixed 2 ⟨τ, hτ⟩ hF]

/-- Endpoint face compatibility identifies every original tetrahedron face value. -/
theorem finiteTwoCapValue_tetrahedron_face (P : PartialSimplexStraightening 1 y S F hS N)
    (hN : 3 < N) (τ : {τ // τ ∈ S 3}) (i : Fin 4) :
    finiteTwoCapValue P (restrictSimplex τ.val (SimplexCategory.δ i)) =
      integralTwoCapValue y
        (restrictSimplex (P.endpoint 3 τ) (SimplexCategory.δ i)) := by
  classical
  change finiteTwoCapValue P (hS.face τ i).val = _
  rw [finiteTwoCapValue, dite_eq_left (hS.face τ i).property]
  exact congrArg (integralTwoCapValue y) (P.endpoint_face 2 hN τ i).symm

/-- The literal differential of a selected original tetrahedron has zero endpoint cap evaluation. -/
theorem finiteTwoCapValue_tetrahedron_boundary
    (P : PartialSimplexStraightening 1 y S F hS N) (hN : 3 < N)
    (τ : {τ // τ ∈ S 3}) (b : ULift.{u} ℤ) :
    integralChainEvaluation 2 (finiteTwoCapValue P)
      ((singularChainComplex (constant Y integralCoefficients.{u})).d 3 2
        (chainInclusion (constant Y integralCoefficients.{u}) τ.val b)) = 0 := by
  rw [integralChainEvaluation_boundary]
  simp only [finiteTwoCapValue_tetrahedron_face P hN τ]
  exact (integralChainEvaluation_boundary 2 (integralTwoCapValue y)
    (P.endpoint 3 τ) b).symm.trans
      (integralTwoCapValue_tetrahedron_boundary (P.endpoint 3 τ)
        (P.endpoint_vertices 3 hN τ) b)

/-- The finite ambient boundary evaluates to zero with every original integral coefficient. -/
theorem finiteTwoCapValue_finite_boundary
    (P : PartialSimplexStraightening 1 y S F hS N) (hN : 3 < N)
    (b : Finset (SingularSimplex Y ⦋3⦌)) (v : ∀ _τ, ULift.{u} ℤ)
    (hb : ∀ τ ∈ b, τ ∈ S 3) :
    integralChainEvaluation 2 (finiteTwoCapValue P)
      ((singularChainComplex (constant Y integralCoefficients.{u})).d 3 2
        (∑ τ ∈ b, chainInclusion (constant Y integralCoefficients.{u}) τ (v τ))) = 0 := by
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro τ hτ
  exact finiteTwoCapValue_tetrahedron_boundary P hN ⟨τ, hb τ hτ⟩ (v τ)

/-- A fixed marked spherical two-cycle evaluates to its original homotopy class. -/
theorem finiteTwoCapValue_sphericalTwoChain
    (P : PartialSimplexStraightening 1 y S F hS N) (a : SphericalSimplex Y y 2)
    (ha : a.val ∈ S 2) (hF : a.val ∈ F 2)
    (hc : ContinuousMap.const _ y ∈ S 2) (hcF : ContinuousMap.const _ y ∈ F 2) :
    integralChainEvaluation 2 (finiteTwoCapValue P) (sphericalTwoChain a) =
      Additive.ofMul a.homotopyClassStick := by
  rw [sphericalTwoChain, map_sub, integralChainEvaluation_inclusion,
    integralChainEvaluation_inclusion, finiteTwoCapValue_fixed P a.val ha hF,
    finiteTwoCapValue_fixed P _ hc hcF, integralTwoCapValue_spherical, integralTwoCapValue_const]
  simp only [one_smul, smul_zero, sub_zero]

end FundamentalGroupoid.LocalCoefficients
