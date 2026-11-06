/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FiniteCycleKEquivalence
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteTermEvaluation
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.BoundedTermsAcyclic
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.CycleEvaluationSequence
public import Colib.Algebra.Homology.CochainComplex.Cycles

/-! # The original finite-stratum acyclic inclusion has adjacent-cycle incidence

The actual inclusion into bounded termwise complexes retains complexes and
chain maps. Original term evaluation after this original inclusion is the
product of the two adjacent original cycle evaluations. Endpoint factors
vanish by genuine term bounds and acyclicity. This computes a nontrivial
inclusion map in the isomorphism weak models; no fibration is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FiniteCycleIncidence.lean` at Quillen commit
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
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A)

/-- The actual inclusion with unchanged complexes and original chain maps. -/
def finiteAcyclicTermsInclusion (a b : ℤ) :
    (fixedAcyclicBounds P a b).FullSubcategory ⥤ (fixedTermsBounds P a b).FullSubcategory :=
  (fixedTermsBounds P a b).lift
    ((fixedAcyclicBounds P a b).ι ⋙ boundedAcyclicTermsInclusion P) (fun K ↦ K.property)

@[simp] theorem finiteAcyclicTermsInclusion_map (a b : ℤ)
    {K L : (fixedAcyclicBounds P a b).FullSubcategory} (f : K ⟶ L) :
    ((finiteAcyclicTermsInclusion P a b).map f).hom.hom = f.hom.hom := rfl

instance finiteAcyclicTermsInclusion_additive (a b : ℤ) :
    (finiteAcyclicTermsInclusion P a b).Additive :=
  inferInstanceAs (Functor.Additive ((fixedTermsBounds P a b).lift _ _))

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance finiteCycleIncidence_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- Exactness for the original inherited conflations requires no kernel closure. -/
def finiteAcyclicTermsExactInclusion (a b : ℤ) :
    ExactCategory.ExactFunctor (fixedAcyclicExactStructure P a b)
      (fixedTermsExactStructure P a b) where
  toFunctor := finiteAcyclicTermsInclusion P a b
  map_conflation _ hS := hS

variable [(abelianExactStructure A).IsKernelClosed P]

/-- The original cycle inclusion, now on a specified actual stratum. -/
def finiteCycleTermInclusion (a b n : ℤ) :
    finiteCycleEvaluation P a b n ⟶ finiteAcyclicTermsInclusion P a b ⋙ finiteTermEvaluation P a
      b n where
  app K := P.homMk (K.obj.obj.iCycles n)
  naturality _ _ f := ObjectProperty.hom_ext _ (cyclesMap_i f.hom.hom n)

/-- The original differential-to-cycles map, now on the same stratum. -/
def finiteCycleTermProjection (a b n : ℤ) :
    finiteAcyclicTermsInclusion P a b ⋙ finiteTermEvaluation P a b n ⟶
      finiteCycleEvaluation P a b (n + 1) where
  app K := P.homMk (K.obj.obj.toCycles n (n + 1))
  naturality _ _ f := ObjectProperty.hom_ext _ (toCycles_naturality f.hom.hom n (n + 1)).symm

omit [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P] in
@[simp] theorem finiteCycleTermInclusion_hom (a b n : ℤ)
    (K : (fixedAcyclicBounds P a b).FullSubcategory) :
    ((finiteCycleTermInclusion P a b n).app K).hom = K.obj.obj.iCycles n := rfl

omit [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P] in
@[simp] theorem finiteCycleTermProjection_hom (a b n : ℤ)
    (K : (fixedAcyclicBounds P a b).FullSubcategory) :
    ((finiteCycleTermProjection P a b n).app K).hom = K.obj.obj.toCycles n (n + 1) := rfl

omit [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P] in
@[reassoc] theorem finiteCycleTerm_comp_zero (a b n : ℤ) :
    finiteCycleTermInclusion P a b n ≫ finiteCycleTermProjection P a b n = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _ (_root_.CochainComplex.iCycles_toCycles K.obj.obj n)

/-- Its component is precisely the original actual cycle short exact sequence. -/
theorem finiteCycleTerm_conflation (a b n : ℤ)
    (K : (fixedAcyclicBounds P a b).FullSubcategory) :
    (ExactSubcategory.exactStructure (abelianExactStructure A) P).conflation
      (ShortComplex.mk ((finiteCycleTermInclusion P a b n).app K)
        ((finiteCycleTermProjection P a b n).app K)
        (NatTrans.congr_app (finiteCycleTerm_comp_zero P a b n) K)) :=
  _root_.CochainComplex.cycleSequence_shortExact K.obj.obj n (K.obj.property.2.2 (n + 1))

/-- The actual incidence sequence has the genuine relative cofibration property. -/
theorem finiteCycleTerm_isCofibrationSequence (a b n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (fixedAcyclicExactStructure P a b))
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P))
      (finiteCycleTermInclusion P a b n) (finiteCycleTermProjection P a b n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (finiteCycleTerm_comp_zero P a b n)
    (finiteCycleTerm_conflation P a b n) (finiteCycleEvaluationExact P a b n)
    ((finiteAcyclicTermsExactInclusion P a b).comp (finiteTermEvaluationExact P a b n))
    (finiteCycleEvaluationExact P a b (n + 1)) rfl rfl rfl

/-- The original term coordinate of the original inclusion is the adjacent-cycle product. -/
theorem finiteCycle_KMap_incidence (a b n : ℤ) (k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k) :
    KMap (finiteTermEvaluationExact P a b n).waldhausenExact k
      (KMap (finiteAcyclicTermsExactInclusion P a b).waldhausenExact k x) =
        KMap (finiteCycleEvaluationExact P a b n).waldhausenExact k x *
          KMap (finiteCycleEvaluationExact P a b (n + 1)).waldhausenExact k x := by
  exact (DFunLike.congr_fun (KMap_comp_KMap
    (finiteAcyclicTermsExactInclusion P a b).waldhausenExact
    (finiteTermEvaluationExact P a b n).waldhausenExact k).symm x).symm.trans
      (Additivity.KMap_additivity_mul _ _ (finiteCycleTermInclusion P a b n)
        (finiteCycleTermProjection P a b n) (finiteCycleTerm_isCofibrationSequence P a b n) k x)

/-- The actual cycle-coordinate K-map vanishes outside the interior interval. -/
theorem finiteCycle_KMap_evaluation_zero (a b n : ℤ) (hn : n ≤ a ∨ b < n) (k : ℕ) :
    KMap (finiteCycleEvaluationExact P a b n).waldhausenExact k = 1 := by
  have he := KMap_eq_of_iso (finiteCycleEvaluationExact P a b n).waldhausenExact
    (zeroFunctor_isExact (ofExactCategory (fixedAcyclicExactStructure P a b))
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)))
    (finiteCycleEvaluationZeroIso P a b n hn) k
  exact he.trans (KMap_zeroFunctor _ _ k)

/-- At the genuine lower term endpoint only the next-cycle coordinate remains. -/
theorem finiteCycle_KMap_incidence_lower (a b : ℤ) (k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k) :
    KMap (finiteTermEvaluationExact P a b a).waldhausenExact k
      (KMap (finiteAcyclicTermsExactInclusion P a b).waldhausenExact k x) =
        KMap (finiteCycleEvaluationExact P a b (a + 1)).waldhausenExact k x := by
  rw [finiteCycle_KMap_incidence, finiteCycle_KMap_evaluation_zero P a b a (Or.inl le_rfl),
    MonoidHom.one_apply, one_mul]

/-- At the genuine upper term endpoint only the preceding disk's cycle remains. -/
theorem finiteCycle_KMap_incidence_upper (a b : ℤ) (k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k) :
    KMap (finiteTermEvaluationExact P a b b).waldhausenExact k
      (KMap (finiteAcyclicTermsExactInclusion P a b).waldhausenExact k x) =
        KMap (finiteCycleEvaluationExact P a b b).waldhausenExact k x := by
  rw [finiteCycle_KMap_incidence, finiteCycle_KMap_evaluation_zero P a b (b + 1) (Or.inr (by
    omega)),
    MonoidHom.one_apply, mul_one]

/-- In the proved finite coordinates, an interior term receives its two adjacent cycles. -/
theorem finiteCycleKEquiv_incidence (a : ℤ) (m k : ℕ) (i j : Fin m)
    (hij : i.val + 1 = j.val)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k) :
    KMap (finiteTermEvaluationExact P a (a + (m : ℤ)) (a + (j : ℤ))).waldhausenExact k
      (KMap (finiteAcyclicTermsExactInclusion P a (a + (m : ℤ))).waldhausenExact k x) =
        finiteCycleKEquiv P a m k x i * finiteCycleKEquiv P a m k x j := by
  have hi : a + (i : ℤ) + 1 = a + (j : ℤ) := by omega
  simpa only [finiteCycleKEquiv_apply, hi] using
    finiteCycle_KMap_incidence P a (a + (m : ℤ)) (a + (j : ℤ)) k x

end CategoryTheory.Waldhausen.GilletWaldhausen
