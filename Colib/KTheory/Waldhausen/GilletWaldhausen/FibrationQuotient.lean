/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Waldhausen.Fibration.LongExactSequence
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FineProductDecomposition
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FibrationModelKEquivalence

/-! # The exact Gillet-Waldhausen quotient and original coarse single map

The genuine fine acyclic-times-single decomposition identifies the quotient
by the original acyclic inclusion with the original degree-zero single KMap.
The actual canonical fiber comparison supplies exactness and surjectivity,
including degree zero. This algebraic layer supports distinct object and hom
universes and retains its explicit canonical-comparison hypothesis.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FibrationQuotient.lean` at Quillen commit
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
universe u v
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]
local instance assembly_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The exact model equivalence transfers the already proved inclusion injectivity. -/
theorem fiberObjectsInclusion_KMap_injective (n : ℕ) :
    Function.Injective (KMap (Fibration.acyclicInclusion_exact (boundedTermsNested P)) n) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (boundedAcyclicFiberKEquiv P n).surjective x
  obtain ⟨b, rfl⟩ := (boundedAcyclicFiberKEquiv P n).surjective y
  have hi := boundedAcyclicTermsInclusion_KMap_injective P n
  apply congrArg (boundedAcyclicFiberKEquiv P n)
  apply hi
  exact (DFunLike.congr_fun (boundedAcyclicFiberKEquiv_inclusion P n) a).symm.trans
    (hxy.trans (DFunLike.congr_fun (boundedAcyclicFiberKEquiv_inclusion P n) b))

/-- The original coarse degree-zero single map is bijective as soon as the
actual change-of-weak map is onto and its kernel is the original acyclic image. -/
theorem boundedTermsSingle_coarse_KMap_bijective_of_exact (n : ℕ)
    (he : (KMap (Fibration.acyclicInclusion_exact (boundedTermsNested P)) n).range =
      (KMap (Fibration.changeWeak_exact (boundedTermsNested P)) n).ker)
    (hs : Function.Surjective (KMap (Fibration.changeWeak_exact (boundedTermsNested P)) n)) :
    Function.Bijective (KMap (boundedTermsSingle_coarseExact P 0) n) := by
  constructor
  · apply (injective_iff_map_eq_one (KMap (boundedTermsSingle_coarseExact P 0) n)).2
    intro x hx
    have hm : KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact n x ∈
        (KMap (Fibration.acyclicInclusion_exact (boundedTermsNested P)) n).range := by
      rw [he]
      change KMap (Fibration.changeWeak_exact (boundedTermsNested P)) n
        (KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact n x) = 1
      rw [← boundedTermsSingle_coarse_KMap_apply]
      exact hx
    obtain ⟨a, ha⟩ := hm
    let b := (boundedAcyclicFiberKEquiv P n).symm a
    have hb : KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact n b =
        KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact n x := by
      rw [← DFunLike.congr_fun (boundedAcyclicFiberKEquiv_inclusion P n) b]
      change KMap (Fibration.acyclicInclusion_exact (boundedTermsNested P)) n
        ((boundedAcyclicFiberKEquiv P n) ((boundedAcyclicFiberKEquiv P n).symm a)) = _
      rw [MulEquiv.apply_symm_apply]
      exact ha
    have hp : boundedTermsAcyclicSingleKEquiv P n (b, 1) =
        boundedTermsAcyclicSingleKEquiv P n (1, x) := by
      simp only [boundedTermsAcyclicSingleKEquiv_apply, map_one, mul_one, one_mul]
      exact hb
    exact (congrArg _root_.Prod.snd ((boundedTermsAcyclicSingleKEquiv P n).injective hp)).symm
  · intro y
    obtain ⟨z, hz⟩ := hs y
    let p := (boundedTermsAcyclicSingleKEquiv P n).symm z
    refine ⟨p.2, ?_⟩
    have h := DFunLike.congr_fun (boundedTermsAcyclicSingleKEquiv_coarse P n) p
    change KMap (Fibration.changeWeak_exact (boundedTermsNested P)) n
      ((boundedTermsAcyclicSingleKEquiv P n) ((boundedTermsAcyclicSingleKEquiv P n).symm z)) =
        KMap (boundedTermsSingle_coarseExact P 0) n p.2 at h
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm.trans hz

/-- The original canonical fiber comparison supplies the K-group
comparison; all algebraic maps, including degree zero, are the original maps. -/
theorem boundedTermsSingle_coarse_KMap_bijective_of_canonicalFiber_weak
    (h : IsWeakHomotopyEquivalence (Fibration.canonicalFiberMap (boundedTermsNested P))) (n : ℕ) :
    Function.Bijective (KMap (boundedTermsSingle_coarseExact P 0) n) :=
  boundedTermsSingle_coarse_KMap_bijective_of_exact P n
    (Fibration.range_acyclicInclusion_eq_ker_changeWeak_of_weak (boundedTermsNested P) h n)
    (Fibration.changeWeak_KMap_surjective_of_weak (boundedTermsNested P) h
      (fiberObjectsInclusion_KMap_injective P) n)

/-- The conditional equivalence's forward homomorphism is the exact original map. -/
def boundedTermsSingleCoarseKEquivOfCanonicalFiberWeakEquivalence
    (h : IsWeakHomotopyEquivalence (Fibration.canonicalFiberMap (boundedTermsNested P))) (n : ℕ) :
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K n ≃*
      (boundedTermsNested P).coarse.K n :=
  MulEquiv.ofBijective (KMap (boundedTermsSingle_coarseExact P 0) n)
    (boundedTermsSingle_coarse_KMap_bijective_of_canonicalFiber_weak P h n)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem boundedTermsSingleCoarseKEquivOfCanonicalFiberWeakEquivalence_coe (h :
    IsWeakHomotopyEquivalence (Fibration.canonicalFiberMap (boundedTermsNested P))) (n : ℕ) :
    (↑(boundedTermsSingleCoarseKEquivOfCanonicalFiberWeakEquivalence P h n) : (ofExactCategory
        (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K n →*
        (boundedTermsNested P).coarse.K n) =
      KMap (boundedTermsSingle_coarseExact P 0) n := rfl


end CategoryTheory.Waldhausen.GilletWaldhausen
