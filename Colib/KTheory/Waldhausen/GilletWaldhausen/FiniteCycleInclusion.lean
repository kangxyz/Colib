/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FiniteCycleIncidence

/-! # Injectivity of the original finite acyclic inclusion K-map

Actual adjacent-cycle incidence and the zero lower cycle recursively detect
all cycle coordinates. The proved finite cycle decomposition then detects the
original class. These are genuine original isomorphism-model KMaps, including
K₀ and empty term intervals, without any fibration assumption.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FiniteCycleInclusion.lean` at Quillen commit
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
local instance finiteCycleInclusion_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The original inclusion detects one in each actual [a,a+m] acyclic stratum. -/
theorem finiteCycleInclusion_KMap_eq_one (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k)
    (hx : KMap (finiteAcyclicTermsExactInclusion P a (a + (m : ℤ))).waldhausenExact k x = 1) :
    x = 1 := by
  have hz (i : ℕ) (hi : i ≤ m) :
      KMap (finiteCycleEvaluationExact P a (a + (m : ℤ)) (a + (i : ℤ))).waldhausenExact k x = 1
        := by
    induction i with
    | zero =>
      rw [finiteCycle_KMap_evaluation_zero P a (a + (m : ℤ)) _ (Or.inl (by omega)),
        MonoidHom.one_apply]
    | succ i ih =>
      have h := finiteCycle_KMap_incidence P a (a + (m : ℤ)) (a + (i : ℤ)) k x
      rw [hx, map_one, ih (by omega), one_mul] at h
      simpa only [Nat.cast_succ, add_assoc] using h.symm
  apply (finiteCycleKEquiv P a m k).injective
  rw [map_one]
  funext i
  change KMap (finiteCycleEvaluationExact P a (a + (m : ℤ))
    (a + (i : ℤ) + 1)).waldhausenExact k x = 1
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hz (i.val + 1) (by omega)

/-- The original acyclic inclusion is genuinely injective for every finite interval. -/
theorem finiteAcyclicTermsInclusion_KMap_injective (a b : ℤ) (k : ℕ) :
    Function.Injective (KMap (finiteAcyclicTermsExactInclusion P a b).waldhausenExact k) := by
  have hker (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k)
      (hx : KMap (finiteAcyclicTermsExactInclusion P a b).waldhausenExact k x = 1) : x = 1 := by
    by_cases hab : a ≤ b
    · have hb : a + ((b - a).toNat : ℤ) = b := by omega
      have h := finiteCycleInclusion_KMap_eq_one P a (b - a).toNat k
      rw [hb] at h
      exact h x hx
    · have h := finiteCycle_KMap_layers P a b 0 (by omega) k x
      simpa using h
  intro x y hxy
  have h := hker (x * y⁻¹) (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
  exact mul_inv_eq_one.mp h

end CategoryTheory.Waldhausen.GilletWaldhausen
