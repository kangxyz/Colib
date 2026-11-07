/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.SingleInsertion
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FiniteEulerReduction
public import Colib.KTheory.Waldhausen.GilletWaldhausen.AcyclicInclusionInjective

/-! # Actual global reduction to an acyclic class and an original degree-zero term

The original single-complex functor and original acyclic inclusion retain all
maps. Actual finite-stage representation, finite Euler reduction at the true
degree-zero coordinate, and eventual equality detection yield the genuine
global group-level reduction. No globally uniform bound or fibration is used.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/GlobalEulerReduction.lean` at Quillen commit
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
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
attribute [local instance] globalEulerReduction_termPropertyProducts

/-- The corresponding original normalized KMaps commute exactly. -/
theorem finiteTermSingle_KMap_inclusion (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) (k : ℕ)
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    KMap (fixedTermsInclusionExactFunctor P a b).waldhausenExact k
      (KMap (finiteTermSingleExact P a b n ha hb).waldhausenExact k x) =
        KMap (boundedTermsSingleExactFunctor P n).waldhausenExact k x := by
  have he := KMap_eq_of_iso ((finiteTermSingleExact P a b n ha hb).waldhausenExact.comp
    (fixedTermsInclusionExactFunctor P a b).waldhausenExact)
    (boundedTermsSingleExactFunctor P n).waldhausenExact
    (eqToIso (finiteTermSingle_comp_inclusion P a b n ha hb)) k
  exact (DFunLike.congr_fun (KMap_comp_KMap (finiteTermSingleExact P a b n ha hb).waldhausenExact
    (fixedTermsInclusionExactFunctor P a b).waldhausenExact k).symm x).symm.trans
      (DFunLike.congr_fun he x)

/-- Actual original single insertion commutes with every increasing bound transition. -/
theorem finiteTermSingle_KMap_transition {N M : ℕ} (h : N ≤ M) (n : ℤ)
    (ha : -(N : ℤ) ≤ n) (hb : n ≤ N) (k : ℕ)
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k
      (KMap (finiteTermSingleExact P (-(N : ℤ)) N n ha hb).waldhausenExact k x) =
        KMap (finiteTermSingleExact P (-(M : ℤ)) M n (by omega) (by omega)).waldhausenExact k x
          := by
  have he : finiteTermSingle P (-(N : ℤ)) N n ha hb ⋙ boundedTermsStratumTransition P h =
      finiteTermSingle P (-(M : ℤ)) M n (by omega) (by omega) := by
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  have hh := KMap_eq_of_iso ((finiteTermSingleExact P (-(N : ℤ)) N n ha hb).waldhausenExact.comp
    (boundedTermsStratumTransitionExact P h).waldhausenExact)
    (finiteTermSingleExact P (-(M : ℤ)) M n (by omega) (by omega)).waldhausenExact (eqToIso he) k
  exact (DFunLike.congr_fun (KMap_comp_KMap
    (finiteTermSingleExact P (-(N : ℤ)) N n ha hb).waldhausenExact
    (boundedTermsStratumTransitionExact P h).waldhausenExact k).symm x).symm.trans
      (DFunLike.congr_fun hh x)

variable [(abelianExactStructure A).IsKernelClosed P]

/-- Integer-bound transport is performed before constructing the actual constrained maps. -/
theorem finiteTerm_existsUnique_acyclic_single_of_bounds (a b n : ℤ) (m k : ℕ)
    (i : Fin (m + 1)) (hb : b = a + (m : ℤ)) (hn : n = a + (i : ℤ))
    (ha : a ≤ n) (hb' : n ≤ b)
    (x : (ofExactCategory (fixedTermsExactStructure P a b)).K k) :
    ∃! p : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k ×
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k,
      KMap (finiteAcyclicTermsExactInclusion P a b).waldhausenExact k p.1 *
        KMap (finiteTermSingleExact P a b n ha hb').waldhausenExact k p.2 = x := by
  subst b
  subst n
  exact finiteTerm_existsUnique_acyclic_single P a m k i x

/-- Pure integer transport identifies the original degree-zero coordinate in a symmetric stratum. -/
theorem symmetricTerms_existsUnique_acyclic_single_zero (N k : ℕ)
    (x : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k) :
    ∃! p : (ofExactCategory (boundedStratumExactStructure P N)).K k ×
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k,
      KMap (finiteAcyclicTermsExactInclusion P (-(N : ℤ)) N).waldhausenExact k p.1 *
        KMap (finiteTermSingleExact P (-(N : ℤ)) N 0 (by omega) (by omega)).waldhausenExact k
          p.2 = x :=
  finiteTerm_existsUnique_acyclic_single_of_bounds P (-(N : ℤ)) N 0 (2 * N) k
    ⟨N, by omega⟩ (by omega) (by simp) (by omega) (by omega) x

/-- Every actual global fine K-class is an original acyclic image times an
original degree-zero single-complex image. -/
theorem boundedTerms_exists_acyclic_single_zero (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    ∃ d : (ofExactCategory (boundedAcyclicExactStructure P)).K k,
      ∃ c : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k,
        KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k d *
          KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k c = x := by
  obtain ⟨N, y, hy⟩ := boundedTerms_KMap_jointlySurjective P k x
  obtain ⟨⟨d, c⟩, hd, _⟩ := symmetricTerms_existsUnique_acyclic_single_zero P N k y
  refine ⟨KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k d, c, ?_⟩
  have he := congrArg (KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k) hd
  rw [map_mul, finiteAcyclicTermsInclusion_KMap_square, finiteTermSingle_KMap_inclusion] at he
  exact he.trans hy

set_option maxHeartbeats 800000 in
-- Extra elaboration budget for transporting finite-stratum K-map identities
-- through transitions and comparing the resulting inclusion composites.
/-- The actual degree-zero representative and actual acyclic class have a trivial joint kernel. -/
theorem boundedTerms_acyclic_single_zero_eq_one (k : ℕ)
    (d : (ofExactCategory (boundedAcyclicExactStructure P)).K k)
    (c : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k)
    (h : KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k d *
      KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k c = 1) : d = 1 ∧ c = 1 := by
  obtain ⟨N, y, hy⟩ := boundedAcyclic_KMap_jointlySurjective P k d
  have hz : KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k
      (KMap (finiteAcyclicTermsExactInclusion P (-(N : ℤ)) N).waldhausenExact k y *
        KMap (finiteTermSingleExact P (-(N : ℤ)) N 0 (by omega) (by omega)).waldhausenExact k c)
          = 1 := by
    rw [map_mul, finiteAcyclicTermsInclusion_KMap_square, finiteTermSingle_KMap_inclusion, hy]
    exact h
  obtain ⟨M, hNM, hh⟩ := boundedTerms_KMap_eq_one_eventually P N k _ hz
  let z := KMap (boundedStratumTransitionExact P hNM).waldhausenExact k y
  have ha := finiteAcyclicTermsInclusion_KMap_transition P hNM k y
  have hb := finiteTermSingle_KMap_transition P hNM 0 (by omega) (by omega) k c
  have hstage :
      KMap (finiteAcyclicTermsExactInclusion P (-(M : ℤ)) M).waldhausenExact k z *
        KMap (finiteTermSingleExact P (-(M : ℤ)) M 0 (by omega) (by omega)).waldhausenExact k c
          = 1 :=
    (congrArg₂ (· * ·) ha hb.symm).trans
      ((map_mul (KMap (boundedTermsStratumTransitionExact P hNM).waldhausenExact k) _
        _).symm.trans hh)
  have hu : (z, c) =
      ((1 : (ofExactCategory (boundedStratumExactStructure P M)).K k),
        (1 : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K
          k)) :=
    (symmetricTerms_existsUnique_acyclic_single_zero P M k 1).unique hstage
      (by simp only [map_one, one_mul])
  have hd : z = 1 := congrArg (fun q :
    (ofExactCategory (boundedStratumExactStructure P M)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k ↦
        q.1) hu
  have hc : c = 1 := congrArg (fun q :
    (ofExactCategory (boundedStratumExactStructure P M)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k ↦
        q.2) hu
  refine ⟨?_, hc⟩
  have hi := DFunLike.congr_fun
    (KMap_comp_KMap (boundedStratumTransitionExact P hNM).waldhausenExact
      (fixedAcyclicInclusionExactFunctor P (-(M : ℤ)) M).waldhausenExact k).symm y
  calc
    d = KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y := hy.symm
    _ = KMap (fixedAcyclicInclusionExactFunctor P (-(M : ℤ)) M).waldhausenExact k
        (KMap (boundedStratumTransitionExact P hNM).waldhausenExact k y) := hi
    _ = 1 := (congrArg
      (KMap (fixedAcyclicInclusionExactFunctor P (-(M : ℤ)) M).waldhausenExact k) hd).trans
        (map_one _)

/-- The actual global representative is unique, retaining both original public KMaps. -/
theorem boundedTerms_existsUnique_acyclic_single_zero (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    ∃! p : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k,
      KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k p.1 *
        KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k p.2 = x := by
  let := Additivity.KCommGroup (ofExactCategory (boundedTermsExactStructure P)) k
  obtain ⟨d, c, hd⟩ := boundedTerms_exists_acyclic_single_zero P k x
  refine ⟨(d, c), hd, ?_⟩
  rintro ⟨d', c'⟩ h'
  have hh : KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k (d' * d⁻¹) *
      KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k (c' * c⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv]
    calc
      _ = (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k d' *
          KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k c') *
          (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k d *
          KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k c)⁻¹ := by
        rw [mul_inv_rev]
        ac_rfl
      _ = 1 := by rw [h', hd, mul_inv_cancel]
  obtain ⟨h₁, h₂⟩ := boundedTerms_acyclic_single_zero_eq_one P k _ _ hh
  exact Prod.ext (mul_inv_eq_one.mp h₁) (mul_inv_eq_one.mp h₂)

end CategoryTheory.Waldhausen.GilletWaldhausen
