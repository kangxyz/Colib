/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FiniteCycleInclusion
public import Colib.KTheory.Waldhausen.GilletWaldhausen.BoundedTermsKCoverage
public import Colib.KTheory.Waldhausen.GilletWaldhausen.BoundedAcyclicKCoverage

/-! # Genuine global injectivity of the original acyclic inclusion K-map

Actual based finite-stage representation and eventual-zero detection reduce
the original global inclusion to its actual finite-stratum inclusion. Finite
cycle incidence detects that class. No categorywide term bound, global
graded equivalence, or fibration theorem is an input.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/AcyclicInclusionInjective.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex


noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]

omit [(abelianExactStructure A).IsKernelClosed P] in
/-- The original finite and global inclusion KMaps form their actual commuting square. -/
theorem finiteAcyclicTermsInclusion_KMap_square (a b : ℤ) (k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k) :
    KMap (fixedTermsInclusionExactFunctor P a b).waldhausenExact k
      (KMap (finiteAcyclicTermsExactInclusion P a b).waldhausenExact k x) =
        KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k
          (KMap (fixedAcyclicInclusionExactFunctor P a b).waldhausenExact k x) := by
  have h₁ := DFunLike.congr_fun (KMap_comp_KMap
    (finiteAcyclicTermsExactInclusion P a b).waldhausenExact
    (fixedTermsInclusionExactFunctor P a b).waldhausenExact k).symm x
  have h₂ := DFunLike.congr_fun (KMap_comp_KMap
    (fixedAcyclicInclusionExactFunctor P a b).waldhausenExact
    (boundedAcyclicTermsExactInclusion P).waldhausenExact k).symm x
  exact h₁.symm.trans h₂

omit [(abelianExactStructure A).IsKernelClosed P] in
/-- Original increasing inclusions commute with the original finite acyclic inclusion KMaps. -/
theorem finiteAcyclicTermsInclusion_KMap_transition {N M : ℕ} (h : N ≤ M) (k : ℕ)
    (x : (ofExactCategory (boundedStratumExactStructure P N)).K k) :
    KMap (finiteAcyclicTermsExactInclusion P (-(M : ℤ)) M).waldhausenExact k
      (KMap (boundedStratumTransitionExact P h).waldhausenExact k x) =
        KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k
          (KMap (finiteAcyclicTermsExactInclusion P (-(N : ℤ)) N).waldhausenExact k x) := by
  have h₁ := DFunLike.congr_fun (KMap_comp_KMap
    (boundedStratumTransitionExact P h).waldhausenExact
    (finiteAcyclicTermsExactInclusion P (-(M : ℤ)) M).waldhausenExact k).symm x
  have h₂ := DFunLike.congr_fun (KMap_comp_KMap
    (finiteAcyclicTermsExactInclusion P (-(N : ℤ)) N).waldhausenExact
    (boundedTermsStratumTransitionExact P h).waldhausenExact k).symm x
  exact h₁.symm.trans h₂

/-- The original global inclusion detects one by actual finite-stage algebra. -/
theorem boundedAcyclicTermsInclusion_KMap_eq_one (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k)
    (hx : KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k x = 1) : x = 1 := by
  obtain ⟨N, y, hy⟩ := boundedAcyclic_KMap_jointlySurjective P k x
  have hz : KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k
      (KMap (finiteAcyclicTermsExactInclusion P (-(N : ℤ)) N).waldhausenExact k y) = 1 := by
    rw [finiteAcyclicTermsInclusion_KMap_square, hy, hx]
  obtain ⟨M, h, hh⟩ := boundedTerms_KMap_eq_one_eventually P N k _ hz
  have he : KMap (boundedStratumTransitionExact P h).waldhausenExact k y = 1 :=
    (finiteAcyclicTermsInclusion_KMap_injective P (-(M : ℤ)) M k)
      (((finiteAcyclicTermsInclusion_KMap_transition P h k y).trans hh).trans (map_one _).symm)
  have hi := DFunLike.congr_fun (KMap_comp_KMap (boundedStratumTransitionExact P h).waldhausenExact
    (fixedAcyclicInclusionExactFunctor P (-(M : ℤ)) M).waldhausenExact k).symm y
  calc
    x = KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y := hy.symm
    _ = KMap (fixedAcyclicInclusionExactFunctor P (-(M : ℤ)) M).waldhausenExact k
        (KMap (boundedStratumTransitionExact P h).waldhausenExact k y) := hi
    _ = 1 := by rw [he, map_one]

/-- Actual global acyclic inclusion is injective on every original K-group, including K₀. -/
theorem boundedAcyclicTermsInclusion_KMap_injective (k : ℕ) :
    Function.Injective (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k) := by
  intro x y hxy
  have h := boundedAcyclicTermsInclusion_KMap_eq_one P k (x * y⁻¹)
    (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
  exact mul_inv_eq_one.mp h

end CategoryTheory.Waldhausen.GilletWaldhausen
