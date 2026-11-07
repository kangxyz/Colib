/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.FiniteCycleFiltration
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula
public import Mathlib.Algebra.BigOperators.Fin

/-! # Actual finite smart-filtration formulas in the original acyclic K-groups

The genuine smart filtration starts at zero already at the lower term bound.
Each original adjacent quotient is the disk on the next actual cycle. Finite
structural additivity therefore computes classes in the isomorphism weak model
as products of their original disk-cycle layers. No acyclic K-group is assumed
trivial, and no global uniform term bound is imposed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FiniteCycleKFormula.lean` at Quillen commit
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
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The original smart upper endpoint induces the identity. -/
theorem finiteCycle_KMap_identity (a b n : ℤ) (hn : b ≤ n) (k : ℕ) :
    KMap (finiteCycleTruncationExact P a b n).waldhausenExact k =
      MonoidHom.id ((ofExactCategory (fixedAcyclicExactStructure P a b)).K k) := by
  have he := KMap_eq_of_iso (finiteCycleTruncationExact P a b n).waldhausenExact
    (IsExact.id (ofExactCategory (fixedAcyclicExactStructure P a b)).cof
      (ofExactCategory (fixedAcyclicExactStructure P a b)).weq)
    (finiteCycleIdentityIso P a b n hn) k
  exact he.trans (KMap_id _ k)

/-- The original lower endpoint is zero by actual acyclicity and actual bounds. -/
theorem finiteCycle_KMap_zero (a b : ℤ) (k : ℕ) :
    KMap (finiteCycleTruncationExact P a b a).waldhausenExact k = 1 := by
  have he := KMap_eq_of_iso (finiteCycleTruncationExact P a b a).waldhausenExact
    (zeroFunctor_isExact (ofExactCategory (fixedAcyclicExactStructure P a b))
      (ofExactCategory (fixedAcyclicExactStructure P a b))) (finiteCycleZeroIso P a b) k
  exact he.trans (KMap_zeroFunctor _ _ k)

/-- Original adjacent smart truncations satisfy literal original-group additivity. -/
theorem finiteCycle_KMap_step (a b n : ℤ) (k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k) :
    KMap (finiteCycleTruncationExact P a b (n + 1)).waldhausenExact k x =
      KMap (finiteCycleTruncationExact P a b n).waldhausenExact k x *
        KMap (finiteCycleLayerExact P a b n).waldhausenExact k x :=
  Additivity.KMap_additivity_mul _ _ (finiteCycleInclusion P a b n)
    (finiteCycleProjection P a b n) (finiteCycle_isCofibrationSequence P a b n) k x

/-- Finite iteration of the genuine structural additivity theorem. -/
theorem finiteCycle_KMap_iterated (a b n : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k) :
    let := Additivity.KCommGroup (ofExactCategory (fixedAcyclicExactStructure P a b)) k
    KMap (finiteCycleTruncationExact P a b (n + (m : ℤ))).waldhausenExact k x =
      KMap (finiteCycleTruncationExact P a b n).waldhausenExact k x *
        ∏ i ∈ Finset.range m, KMap (finiteCycleLayerExact P a b (n + (i : ℤ))).waldhausenExact k
          x := by
  let := Additivity.KCommGroup (ofExactCategory (fixedAcyclicExactStructure P a b)) k
  induction m with
  | zero => simp
  | succ m ih =>
    have he : n + ((m + 1 : ℕ) : ℤ) = (n + (m : ℤ)) + 1 := by omega
    rw [he, finiteCycle_KMap_step P a b (n + (m : ℤ)) k x, ih]
    simp only [Finset.prod_range_succ, mul_assoc]

/-- Every actual class in a specified acyclic stratum is the finite product
of the original disks on its interior cycles. The empty product is included. -/
theorem finiteCycle_KMap_layers (a b : ℤ) (m : ℕ) (hm : b ≤ a + (m : ℤ)) (k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k) :
    let := Additivity.KCommGroup (ofExactCategory (fixedAcyclicExactStructure P a b)) k
    x = ∏ i : Fin m, KMap (finiteCycleLayerExact P a b (a + (i : ℤ))).waldhausenExact k x := by
  let := Additivity.KCommGroup (ofExactCategory (fixedAcyclicExactStructure P a b)) k
  have h := finiteCycle_KMap_iterated P a b a m k x
  rw [finiteCycle_KMap_identity P a b _ hm k, finiteCycle_KMap_zero P a b k] at h
  simpa only [MonoidHom.id_apply, MonoidHom.one_apply, one_mul, Finset.prod_range] using h

end CategoryTheory.Waldhausen.GilletWaldhausen
