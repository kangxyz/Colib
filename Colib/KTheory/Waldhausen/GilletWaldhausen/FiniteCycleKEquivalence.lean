/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteCycleEvaluation
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FiniteCycleKFormula

/-! # Genuine finite cycle K-decomposition

For actual acyclic term bounds [a,a+m], the original cycle evaluation maps
at degrees a+1,...,a+m identify the isomorphism-weak K-group with m copies
of the original K-group of P. The inverse is the literal finite product of
original identity-disk insertions in degrees a+i,a+i+1. The endpoint cycle
vanishing and both inverse identities are proved, including m=0 and K₀.

The mixed evaluation/insertion K-map API requires the explicitly displayed
compatible object universe `A : Type (max u v)` and hom universe v.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FiniteCycleKEquivalence.lean` at Quillen commit
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
local instance finiteCycleKEquivalence_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- Original evaluation after original same-degree insertion induces the identity. -/
theorem finiteCycle_KMap_disk_self (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b) (k : ℕ)
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    KMap (finiteCycleEvaluationExact P a b (n + 1)).waldhausenExact k
      (KMap (finiteCycleDiskExact P a b n ha hb).waldhausenExact k x) = x := by
  have h := KMap_eq_of_iso
    ((finiteCycleDiskExact P a b n ha hb).waldhausenExact.comp
      (finiteCycleEvaluationExact P a b (n + 1)).waldhausenExact)
    (IsExact.id (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).cof
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).weq)
    (finiteCycleDiskEvaluationIso P a b n ha hb) k
  exact (DFunLike.congr_fun (KMap_comp_KMap
    (finiteCycleDiskExact P a b n ha hb).waldhausenExact
    (finiteCycleEvaluationExact P a b (n + 1)).waldhausenExact k).symm x).symm.trans (by
      simpa only [KMap_id, MonoidHom.id_apply] using DFunLike.congr_fun h x)

/-- Different-degree evaluation of the actual insertion induces the trivial map. -/
theorem finiteCycle_KMap_disk_ne (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b)
    (j : ℤ) (hj : j ≠ n + 1) (k : ℕ)
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    KMap (finiteCycleEvaluationExact P a b j).waldhausenExact k
      (KMap (finiteCycleDiskExact P a b n ha hb).waldhausenExact k x) = 1 := by
  let W := ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)
  have h := KMap_eq_of_iso
    ((finiteCycleDiskExact P a b n ha hb).waldhausenExact.comp
      (finiteCycleEvaluationExact P a b j).waldhausenExact)
    (zeroFunctor_isExact W W) (finiteCycleDiskEvaluationZeroIso P a b n ha hb j hj) k
  exact (DFunLike.congr_fun (KMap_comp_KMap
    (finiteCycleDiskExact P a b n ha hb).waldhausenExact
    (finiteCycleEvaluationExact P a b j).waldhausenExact k).symm x).symm.trans (by
      simpa only [KMap_zeroFunctor, MonoidHom.one_apply] using DFunLike.congr_fun h x)

/-- The actual disk-layer K-map factors through the original term category. -/
theorem finiteCycle_KMap_layer_factor (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b) (k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k) :
    KMap (finiteCycleDiskExact P a b n ha hb).waldhausenExact k
      (KMap (finiteCycleEvaluationExact P a b (n + 1)).waldhausenExact k x) =
        KMap (finiteCycleLayerExact P a b n).waldhausenExact k x := by
  have h := KMap_eq_of_iso
    ((finiteCycleEvaluationExact P a b (n + 1)).waldhausenExact.comp
      (finiteCycleDiskExact P a b n ha hb).waldhausenExact)
    (finiteCycleLayerExact P a b n).waldhausenExact
    (eqToIso (finiteCycleEvaluation_disk P a b n ha hb)) k
  exact (DFunLike.congr_fun (KMap_comp_KMap
    (finiteCycleEvaluationExact P a b (n + 1)).waldhausenExact
    (finiteCycleDiskExact P a b n ha hb).waldhausenExact k).symm x).symm.trans
      (DFunLike.congr_fun h x)

/-- The tuple consists precisely of the original cycle evaluation K-maps. -/
def finiteCycleEvaluationKMap (a : ℤ) (m k : ℕ) :
    (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k →*
      (Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K
        k) :=
  MonoidHom.pi (fun i ↦ KMap (finiteCycleEvaluationExact P a (a + (m : ℤ))
    (a + (i : ℤ) + 1)).waldhausenExact k)

/-- Each insertion is the original disk-complex K-map at that actual degree. -/
def finiteCycleInsertionKMap (a : ℤ) (m k : ℕ) (i : Fin m) :
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k →*
      (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k :=
  KMap (finiteCycleDiskExact P a (a + (m : ℤ)) (a + (i : ℤ))
    (by omega) (by have := i.isLt; omega)).waldhausenExact k

/-- Reassembly multiplies the actual original disk-insertion K-maps. -/
def finiteCycleReassemble (a : ℤ) (m k : ℕ)
    (x : Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A)
      P)).K k) :
    (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k :=
  let := Additivity.KCommGroup (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))) k
  ∏ i, finiteCycleInsertionKMap P a m k i (x i)

/-- Genuine finite additivity proves reassembly after evaluation is the original identity. -/
theorem finiteCycleReassemble_evaluate (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k) :
    finiteCycleReassemble P a m k (finiteCycleEvaluationKMap P a m k x) = x := by
  let := Additivity.KCommGroup (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))) k
  have h := finiteCycle_KMap_layers P a (a + (m : ℤ)) m (by omega) k x
  apply Eq.trans _ h.symm
  apply Finset.prod_congr rfl
  intro i hi
  exact finiteCycle_KMap_layer_factor P a (a + (m : ℤ)) (a + (i : ℤ))
    (by omega) (by have := i.isLt; omega) k x

set_option maxHeartbeats 800000 in
-- Extra elaboration budget for the product rewrites through exact K-maps and the
-- degree bounds in the disk evaluation/insertion identities.
/-- The actual evaluation/insertion delta identities prove the reverse composite. -/
theorem finiteCycleEvaluate_reassemble (a : ℤ) (m k : ℕ)
    (x : Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A)
      P)).K k) :
    finiteCycleEvaluationKMap P a m k (finiteCycleReassemble P a m k x) = x := by
  let := Additivity.KCommGroup (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))) k
  let := Additivity.KCommGroup
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)) k
  funext j
  change KMap (finiteCycleEvaluationExact P a (a + (m : ℤ))
    (a + (j : ℤ) + 1)).waldhausenExact k
      (∏ i, finiteCycleInsertionKMap P a m k i (x i)) = x j
  rw [map_prod]
  rw [Finset.prod_eq_single j]
  · exact finiteCycle_KMap_disk_self P a (a + (m : ℤ)) (a + (j : ℤ))
      (by omega) (by have := j.isLt; omega) k (x j)
  · intro i hi hij
    exact finiteCycle_KMap_disk_ne P a (a + (m : ℤ)) (a + (i : ℤ))
      (by omega) (by have := i.isLt; omega) (a + (j : ℤ) + 1)
      (by intro he; apply hij; apply Fin.ext; omega) k (x i)
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- Actual finite interior-cycle K-decomposition, including m=0 and K₀. -/
def finiteCycleKEquiv (a : ℤ) (m k : ℕ) :
    (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k ≃*
      (Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K
        k) where
  toFun := finiteCycleEvaluationKMap P a m k
  invFun := finiteCycleReassemble P a m k
  left_inv := finiteCycleReassemble_evaluate P a m k
  right_inv := finiteCycleEvaluate_reassemble P a m k
  map_mul' := (finiteCycleEvaluationKMap P a m k).map_mul

/-- Its forward map is exactly the tuple of original evaluation K-maps. -/
@[simp] theorem finiteCycleKEquiv_apply (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k) (i : Fin m) :
    finiteCycleKEquiv P a m k x i = KMap (finiteCycleEvaluationExact P a (a + (m : ℤ))
      (a + (i : ℤ) + 1)).waldhausenExact k x := rfl

/-- Its inverse is exactly the displayed original-insertion reassembly. -/
@[simp] theorem finiteCycleKEquiv_symm_apply (a : ℤ) (m k : ℕ)
    (x : Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A)
      P)).K k) :
    (finiteCycleKEquiv P a m k).symm x = finiteCycleReassemble P a m k x := rfl

end CategoryTheory.Waldhausen.GilletWaldhausen
