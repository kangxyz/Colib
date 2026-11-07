/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FiniteCycleIncidence
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FiniteTermKEquivalence
public import Colib.Algebra.Group.FiniteAdjacentSection

/-! # Actual finite Euler reduction at any original term coordinate

The original finite term and cycle equivalences identify the actual acyclic
inclusion with the proved adjacent-incidence map. Original single-complex
insertion is the literal single-coordinate map. The proved group calculation
therefore gives a unique actual acyclic class times an actual single-term
class representing each finite termwise class. No fibration is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FiniteEulerReduction.lean` at Quillen commit
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
local instance finiteEulerReduction_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- Transport only the stated integer upper bound, retaining the original evaluation maps. -/
def finiteTermKEquivWithUpper (a b : ℤ) (m k : ℕ) (hb : b = a + (m : ℤ) - 1) :
    (ofExactCategory (fixedTermsExactStructure P a b)).K k ≃*
      (Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K
        k) := by
  subst b
  exact finiteTermKEquiv P a m k

@[simp] theorem finiteTermKEquivWithUpper_apply (a b : ℤ) (m k : ℕ)
    (hb : b = a + (m : ℤ) - 1)
    (x : (ofExactCategory (fixedTermsExactStructure P a b)).K k) (i : Fin m) :
    finiteTermKEquivWithUpper P a b m k hb x i =
      KMap (finiteTermEvaluationExact P a b (a + (i : ℤ))).waldhausenExact k x := by
  subst b
  rfl

/-- The original term equivalence for the closed interval with m+1 actual terms. -/
def finiteTermKEquivClosed (a : ℤ) (m k : ℕ) :
    (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ)))).K k ≃*
      (Fin (m + 1) → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A)
        P)).K k) :=
  finiteTermKEquivWithUpper P a (a + (m : ℤ)) (m + 1) k (by omega)

@[simp] theorem finiteTermKEquivClosed_apply (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ)))).K k) (i : Fin (m + 1)) :
    finiteTermKEquivClosed P a m k x i =
      KMap (finiteTermEvaluationExact P a (a + (m : ℤ)) (a + (i : ℤ))).waldhausenExact k x :=
  finiteTermKEquivWithUpper_apply P a (a + (m : ℤ)) (m + 1) k (by omega) x i

/-- Original single insertion is precisely the literal original single-coordinate group map. -/
theorem finiteTermKEquivClosed_single (a : ℤ) (m k : ℕ) (i : Fin (m + 1))
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    let := Additivity.KCommGroup
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)) k
    finiteTermKEquivClosed P a m k
      (KMap (finiteTermSingleExact P a (a + (m : ℤ)) (a + (i : ℤ))
        (by omega) (by have := i.isLt; omega)).waldhausenExact k x) =
      MonoidHom.FiniteAdjacentComplex.singleCoordinate
        ((ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) i
          x := by
  let := Additivity.KCommGroup
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)) k
  funext j
  rw [finiteTermKEquivClosed_apply, MonoidHom.FiniteAdjacentComplex.singleCoordinate_apply]
  by_cases hji : j = i
  · subst j
    simpa using finiteTerm_KMap_single_self.{v,u} P a (a + (m : ℤ)) (a + (i : ℤ))
      (by omega) (by have := i.isLt; omega) k x
  · have hn : a + (j : ℤ) ≠ a + (i : ℤ) := by intro he; apply hji; apply Fin.ext; omega
    simpa [Pi.mulSingle_apply, hji] using
      finiteTerm_KMap_single_ne.{v,u} P a (a + (m : ℤ)) (a + (i : ℤ))
        (by omega) (by have := i.isLt; omega) (a + (j : ℤ)) hn k x

variable [(abelianExactStructure A).IsKernelClosed P]

/-- The original finite inclusion is exactly the original adjacent-incidence map
in the proved term and cycle coordinates, including both boundary coordinates. -/
theorem finiteTermKEquivClosed_incidence (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k) :
    let := Additivity.KCommGroup
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)) k
    finiteTermKEquivClosed P a m k
      (KMap (finiteAcyclicTermsExactInclusion P a (a + (m : ℤ))).waldhausenExact k x) =
        MonoidHom.FiniteAdjacentComplex.incidence
          ((ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) m
          (finiteCycleKEquiv P a m k x) := by
  let := Additivity.KCommGroup
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)) k
  have hp (j : Fin (m + 1)) :
      KMap (finiteCycleEvaluationExact P a (a + (m : ℤ)) (a + (j : ℤ))).waldhausenExact k x =
        (Fin.cons 1 (finiteCycleKEquiv P a m k x) : Fin (m + 1) →
          (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) j
            := by
    cases j using Fin.cases with
    | zero =>
      exact DFunLike.congr_fun (finiteCycle_KMap_evaluation_zero P a (a + (m : ℤ))
        (a + ((0 : Fin (m + 1)) : ℤ)) (Or.inl (by simp)) k) x
    | succ j => simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.cons_succ,
        finiteCycleKEquiv_apply, add_assoc]
  have hn (j : Fin (m + 1)) :
      KMap (finiteCycleEvaluationExact P a (a + (m : ℤ)) (a + (j : ℤ) + 1)).waldhausenExact k x =
        (Fin.snoc (finiteCycleKEquiv P a m k x) 1 : Fin (m + 1) →
          (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) j
            := by
    cases j using Fin.lastCases with
    | last =>
      simp only [Fin.val_last, Fin.snoc_last]
      rw [finiteCycle_KMap_evaluation_zero P a (a + (m : ℤ)) _ (Or.inr (by omega)),
        MonoidHom.one_apply]
    | cast j => simp only [Fin.val_castSucc, Fin.snoc_castSucc, finiteCycleKEquiv_apply]
  funext j
  rw [finiteTermKEquivClosed_apply, finiteCycle_KMap_incidence,
    MonoidHom.FiniteAdjacentComplex.incidence_apply, hp, hn]

/-- Every actual finite term class has a unique original acyclic class times
an original single-term class in any specified allowed coordinate. -/
theorem finiteTerm_existsUnique_acyclic_single (a : ℤ) (m k : ℕ) (i : Fin (m + 1))
    (x : (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ)))).K k) :
    ∃! p : (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k ×
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k,
      KMap (finiteAcyclicTermsExactInclusion P a (a + (m : ℤ))).waldhausenExact k p.1 *
        KMap (finiteTermSingleExact P a (a + (m : ℤ)) (a + (i : ℤ))
          (by omega) (by have := i.isLt; omega)).waldhausenExact k p.2 = x := by
  let := Additivity.KCommGroup
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)) k
  obtain ⟨⟨d, c⟩, hd, hu⟩ := MonoidHom.FiniteAdjacentComplex.existsUnique_incidence_coordinate
    ((ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) m i
    (finiteTermKEquivClosed P a m k x)
  refine ⟨((finiteCycleKEquiv P a m k).symm d, c), ?_, ?_⟩
  · apply (finiteTermKEquivClosed P a m k).injective
    rw [map_mul, finiteTermKEquivClosed_incidence, MulEquiv.apply_symm_apply,
      finiteTermKEquivClosed_single]
    exact hd
  · rintro ⟨d', c'⟩ h
    have he := congrArg (finiteTermKEquivClosed P a m k) h
    rw [map_mul, finiteTermKEquivClosed_incidence, finiteTermKEquivClosed_single] at he
    have hu' := hu (finiteCycleKEquiv P a m k d', c') he
    apply Prod.ext
    · apply (finiteCycleKEquiv P a m k).injective
      have hd' : finiteCycleKEquiv P a m k d' = d :=
        congrArg (fun q : (Fin m → (ofExactCategory (ExactSubcategory.exactStructure
          (abelianExactStructure A) P)).K k) ×
          (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k ↦
            q.1) hu'
      exact hd'.trans ((finiteCycleKEquiv P a m k).apply_symm_apply d).symm
    · exact congrArg (fun q : (Fin m →
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) ×
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k ↦
          q.2) hu'

end CategoryTheory.Waldhausen.GilletWaldhausen
