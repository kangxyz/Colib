/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FiniteCapDescent
public import Colib.Topology.LocalCoefficients.ChainSupport
public import Colib.Algebra.Homology.ChainComplex.ModuleCat

/-!
# Actual H-two surjectivity kills the original connecting image after abelianization

Lift the homology class of the marked original absolute spherical cycle by the
original H-two map. The categorical homology quotient supplies an actual chain
boundary for the difference of the original cycles. Finite coproduct support
then gives precisely the equation used by the proved finite cap descent.
The conclusion concerns the unchanged original connecting homomorphism.
-/

/-! Implementation source: `Quillen/Topology/LocalCoefficients/H2CapDescent.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native singular chains,
ordered cap evaluation and original connecting homomorphism are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Topology Convexity.StdSimplex
open scoped Simplicial Topology
universe u

namespace FundamentalGroupoid.LocalCoefficients
open HomotopyFiber
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [PathConnectedSpace X] [SimplyConnectedSpace Y]
variable (j : C(X, Y)) (hj : Function.Injective j) (x : X)

include hj in
/-- Original H-two surjectivity kills every marked original spherical connecting class. -/
theorem connectingAbelianization_spherical_zero_of_h2_surjective
    (hH : Function.Surjective (pushforwardHomologyMap j
      (constant Y integralCoefficients.{u}) 2)) (a : SphericalSimplex Y (j x) 2) :
    connectingAbelianization j x (Additive.ofMul a.homotopyClassStick) = 0 := by
  let A := constant Y integralCoefficients.{u}
  let K := singularChainComplex (constant X integralCoefficients.{u})
  let L := singularChainComplex A
  let q := pushforwardChainMap j A
  let z := sphericalTwoCycle a
  obtain ⟨cH, hcH⟩ := hH (L.homologyπ 2 z)
  obtain ⟨cZ, c, v, hcZ, hc⟩ := homology_exists_finite_cycle
    (constant X integralCoefficients.{u}) 2 cH
  let r : L.cycles 2 := z - HomologicalComplex.cyclesMap q 2 cZ
  have hr : L.homologyπ 2 r = 0 := by
    change L.homologyπ 2 (z - HomologicalComplex.cyclesMap q 2 cZ) = 0
    rw [map_sub]
    have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality q 2) cZ
    change HomologicalComplex.homologyMap q 2 (K.homologyπ 2 cZ) =
      L.homologyπ 2 (HomologicalComplex.cyclesMap q 2 cZ) at hn
    rw [← hn, hcZ]
    exact sub_eq_zero.mpr hcH.symm
  obtain ⟨bC, hbC⟩ := ChainComplex.exists_boundary_of_homologyπ_eq_zero L 2 r hr
  obtain ⟨b, w, hb⟩ := chain_exists_finite_sum A ⦋3⦌ bC
  have hcycle : K.d 2 1
      (∑ τ ∈ c, chainInclusion (constant X integralCoefficients.{u}) τ (v τ)) = 0 := by
    rw [← hc]
    exact ConcreteCategory.congr_hom (K.iCycles_d 2 1) cZ
  have heq : L.d 3 2 (∑ τ ∈ b, chainInclusion A τ (w τ)) =
      sphericalTwoChain a - q.f 2
        (∑ τ ∈ c, chainInclusion (constant X integralCoefficients.{u}) τ (v τ)) := by
    rw [← hb, hbC]
    change L.iCycles 2 (z - HomologicalComplex.cyclesMap q 2 cZ) = _
    rw [map_sub, iCycles_sphericalTwoCycle]
    have hn := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i q 2) cZ
    change L.iCycles 2 (HomologicalComplex.cyclesMap q 2 cZ) = q.f 2 (K.iCycles 2 cZ) at hn
    rw [hn, hc]
  exact connectingAbelianization_zero_of_finite_chain_equation j hj x a c v b w hcycle heq

include hj in
/-- The original connecting map is zero after abelianization, using actual H-two surjectivity. -/
theorem connectingAbelianization_zero_of_h2_surjective
    (hH : Function.Surjective (pushforwardHomologyMap j
      (constant Y integralCoefficients.{u}) 2)) (a : HomotopyGroup.Pi 2 Y (j x)) :
    connectingAbelianization j x (Additive.ofMul a) = 0 := by
  obtain ⟨s, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective a
  exact connectingAbelianization_spherical_zero_of_h2_surjective j hj x hH s

include hj in
/-- Every original connecting class belongs to the commutator subgroup of the actual fiber group. -/
theorem range_connectingHom_le_commutator_of_h2_surjective
    (hH : Function.Surjective (pushforwardHomologyMap j
      (constant Y integralCoefficients.{u}) 2)) :
    (connectingHom j (j x) x rfl 0).range ≤
      commutator (HomotopyGroup.Pi 1 (HomotopyFiber j (j x))
        (HomotopyFiber.basepoint j (j x) x rfl)) := by
  rintro _ ⟨a, rfl⟩
  rw [← Abelianization.ker_of]
  exact connectingAbelianization_zero_of_h2_surjective j hj x hH a

end FundamentalGroupoid.LocalCoefficients
