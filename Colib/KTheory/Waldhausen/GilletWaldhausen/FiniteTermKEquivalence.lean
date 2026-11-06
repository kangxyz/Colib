/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteTermEvaluation
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FiniteTermKFormula

/-! # Genuine finite termwise K-decomposition

The original evaluation K-maps identify the isomorphism-weak K-theory of the
actual stratum [a,a+m-1] with the finite product of the original K-groups of P.
The inverse is the literal finite product of the original single-insertion
K-maps. Empty intervals and K₀ are included. No equivalence is an input.

The mixed evaluation/insertion K-map API uses a common object universe;
`A : Type (max u v)` keeps this explicit while allowing independent hom
universe v, including the usual sheaf-category presentation.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FiniteTermKEquivalence.lean` at Quillen commit
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
local instance finiteTermKEquivalence_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- Original evaluation after original same-degree insertion induces the identity. -/
theorem finiteTerm_KMap_single_self (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) (k : ℕ)
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    KMap (finiteTermEvaluationExact P a b n).waldhausenExact k
      (KMap (finiteTermSingleExact P a b n ha hb).waldhausenExact k x) = x := by
  have h := KMap_eq_of_iso
    ((finiteTermSingleExact P a b n ha hb).waldhausenExact.comp
      (finiteTermEvaluationExact P a b n).waldhausenExact)
    (IsExact.id (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).cof
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).weq)
    (finiteTermSingleEvaluationIso P a b n ha hb) k
  exact (DFunLike.congr_fun (KMap_comp_KMap
    (finiteTermSingleExact P a b n ha hb).waldhausenExact
    (finiteTermEvaluationExact P a b n).waldhausenExact k).symm x).symm.trans (by
      simpa only [KMap_id, MonoidHom.id_apply] using DFunLike.congr_fun h x)

/-- Different-degree evaluation of the actual insertion induces the trivial map. -/
theorem finiteTerm_KMap_single_ne (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b)
    (j : ℤ) (hj : j ≠ n) (k : ℕ)
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    KMap (finiteTermEvaluationExact P a b j).waldhausenExact k
      (KMap (finiteTermSingleExact P a b n ha hb).waldhausenExact k x) = 1 := by
  let W := ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)
  have h := KMap_eq_of_iso
    ((finiteTermSingleExact P a b n ha hb).waldhausenExact.comp
      (finiteTermEvaluationExact P a b j).waldhausenExact)
    (zeroFunctor_isExact W W) (finiteTermSingleEvaluationZeroIso P a b n ha hb j hj) k
  exact (DFunLike.congr_fun (KMap_comp_KMap
    (finiteTermSingleExact P a b n ha hb).waldhausenExact
    (finiteTermEvaluationExact P a b j).waldhausenExact k).symm x).symm.trans (by
      simpa only [KMap_zeroFunctor, MonoidHom.one_apply] using DFunLike.congr_fun h x)

/-- The actual single-layer K-map factors through the original term category. -/
theorem finiteTerm_KMap_layer_factor (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) (k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a b)).K k) :
    KMap (finiteTermSingleExact P a b n ha hb).waldhausenExact k
      (KMap (finiteTermEvaluationExact P a b n).waldhausenExact k x) =
        KMap (finiteTermLayerExact P a b n).waldhausenExact k x := by
  have h := KMap_eq_of_iso
    ((finiteTermEvaluationExact P a b n).waldhausenExact.comp
      (finiteTermSingleExact P a b n ha hb).waldhausenExact)
    (finiteTermLayerExact P a b n).waldhausenExact
    (eqToIso (finiteTermEvaluation_single P a b n ha hb)) k
  exact (DFunLike.congr_fun (KMap_comp_KMap
    (finiteTermEvaluationExact P a b n).waldhausenExact
    (finiteTermSingleExact P a b n ha hb).waldhausenExact k).symm x).symm.trans
      (DFunLike.congr_fun h x)

/-- The tuple consists precisely of the original degreewise evaluation K-maps. -/
def finiteTermEvaluationKMap (a : ℤ) (m k : ℕ) :
    (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k →*
      (Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K
        k) :=
  MonoidHom.pi (fun i ↦ KMap (finiteTermEvaluationExact P a (a + (m : ℤ) - 1)
    (a + (i : ℤ))).waldhausenExact k)

/-- Each insertion is the original single-complex K-map at that actual degree. -/
def finiteTermInsertionKMap (a : ℤ) (m k : ℕ) (i : Fin m) :
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k →*
      (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k :=
  KMap (finiteTermSingleExact P a (a + (m : ℤ) - 1) (a + (i : ℤ))
    (by omega) (by have := i.isLt; omega)).waldhausenExact k

/-- Reassembly multiplies the actual original single-insertion K-maps. -/
def finiteTermReassemble (a : ℤ) (m k : ℕ)
    (x : Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A)
      P)).K k) :
    (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k :=
  let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))) k
  ∏ i, finiteTermInsertionKMap P a m k i (x i)

/-- Genuine finite additivity proves reassembly after evaluation is the original identity. -/
theorem finiteTermReassemble_evaluate (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k) :
    finiteTermReassemble P a m k (finiteTermEvaluationKMap P a m k x) = x := by
  let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))) k
  have h := finiteTerm_KMap_layers P a (a + (m : ℤ) - 1) m (by omega) k x
  apply Eq.trans _ h.symm
  apply Finset.prod_congr rfl
  intro i hi
  exact finiteTerm_KMap_layer_factor P a (a + (m : ℤ) - 1) (a + (i : ℤ))
    (by omega) (by have := i.isLt; omega) k x

set_option maxHeartbeats 800000 in
-- Extra elaboration budget for the product rewrites through exact K-maps and the
-- degree bounds in the single evaluation/insertion identities.
/-- The actual evaluation/insertion delta identities prove the reverse composite. -/
theorem finiteTermEvaluate_reassemble (a : ℤ) (m k : ℕ)
    (x : Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A)
      P)).K k) :
    finiteTermEvaluationKMap P a m k (finiteTermReassemble P a m k x) = x := by
  let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))) k
  let := Additivity.KCommGroup
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)) k
  funext j
  change KMap (finiteTermEvaluationExact P a (a + (m : ℤ) - 1)
    (a + (j : ℤ))).waldhausenExact k
      (∏ i, finiteTermInsertionKMap P a m k i (x i)) = x j
  rw [map_prod]
  rw [Finset.prod_eq_single j]
  · exact finiteTerm_KMap_single_self P a (a + (m : ℤ) - 1) (a + (j : ℤ))
      (by omega) (by have := j.isLt; omega) k (x j)
  · intro i hi hij
    exact finiteTerm_KMap_single_ne P a (a + (m : ℤ) - 1) (a + (i : ℤ))
      (by omega) (by have := i.isLt; omega) (a + (j : ℤ))
      (by intro he; apply hij; apply Fin.ext; omega) k (x i)
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- Actual finite termwise K-decomposition, including empty intervals and K₀. -/
def finiteTermKEquiv (a : ℤ) (m k : ℕ) :
    (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k ≃*
      (Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K
        k) where
  toFun := finiteTermEvaluationKMap P a m k
  invFun := finiteTermReassemble P a m k
  left_inv := finiteTermReassemble_evaluate P a m k
  right_inv := finiteTermEvaluate_reassemble P a m k
  map_mul' := (finiteTermEvaluationKMap P a m k).map_mul

/-- Its forward map is exactly the tuple of original evaluation K-maps. -/
@[simp] theorem finiteTermKEquiv_apply (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k) (i : Fin m) :
    finiteTermKEquiv P a m k x i = KMap (finiteTermEvaluationExact P a (a + (m : ℤ) - 1)
      (a + (i : ℤ))).waldhausenExact k x := rfl

/-- Its inverse is exactly the displayed original-insertion reassembly. -/
@[simp] theorem finiteTermKEquiv_symm_apply (a : ℤ) (m k : ℕ)
    (x : Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A)
      P)).K k) :
    (finiteTermKEquiv P a m k).symm x = finiteTermReassemble P a m k x := rfl

end CategoryTheory.Waldhausen.GilletWaldhausen
