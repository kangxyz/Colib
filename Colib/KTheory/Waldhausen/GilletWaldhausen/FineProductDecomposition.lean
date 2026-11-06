/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Waldhausen.GilletWaldhausen.SingleQuasiComparison
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap

/-! # Actual fine K-product decomposition and its coarse projection

The forward product map is literally the original acyclic-inclusion KMap
times the original degree-zero single-insertion KMap. Genuine unique global
factorization makes it a group equivalence. The already proved weak-natural
null composite shows that changing to quasi-isomorphisms retains exactly the
original coarse single map on the P-coordinate. No fibration exactness or
coarse-map surjectivity is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FineProductDecomposition.lean` at Quillen commit
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
local instance fineProductDecomposition_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The original bounded-acyclic inclusion has trivial coarse composite,
derived from the actual weak-natural nullhomotopy, without a fibration input. -/
theorem boundedAcyclicTerms_changeWeak_KMap (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k) :
    KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k
      (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k x) = 1 := by
  have he := KMap_eq_of_iso
    ((boundedAcyclicToFiberObjects_exact P).comp (Fibration.acyclicInclusion_exact
        (boundedTermsNested P)))
    (boundedAcyclicTermsExactInclusion P).waldhausenExact
    (eqToIso (boundedAcyclicToFiberObjects_comp_inclusion P)) k
  have hi := (DFunLike.congr_fun he x).symm.trans
    (DFunLike.congr_fun (KMap_comp_KMap (boundedAcyclicToFiberObjects_exact P)
      (Fibration.acyclicInclusion_exact (boundedTermsNested P)) k).symm x)
  exact (congrArg (KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k) hi).trans
    (DFunLike.congr_fun (Fibration.changeWeak_KMap_comp_acyclic (boundedTermsNested P) k)
      (KMap (boundedAcyclicToFiberObjects_exact P) k x))

/-- The actual product homomorphism uses the two original public KMaps. -/
def boundedTermsAcyclicSingleKMap (k : ℕ) :
    ((ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) →*
        (ofExactCategory (boundedTermsExactStructure P)).K k :=
  let := Additivity.KCommGroup (ofExactCategory (boundedTermsExactStructure P)) k
  (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k).comp (MonoidHom.fst _ _) *
    (KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k).comp (MonoidHom.snd _ _)

@[simp] theorem boundedTermsAcyclicSingleKMap_apply (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    boundedTermsAcyclicSingleKMap P k x =
      KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k x.1 *
        KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k x.2 := rfl

/-- The actual product's coarse image is exactly the original coarse single map. -/
theorem boundedTermsAcyclicSingleKMap_coarse (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k
      (boundedTermsAcyclicSingleKMap P k x) = KMap (boundedTermsSingle_coarseExact P 0) k x.2 := by
  rw [boundedTermsAcyclicSingleKMap_apply, map_mul, boundedAcyclicTerms_changeWeak_KMap, one_mul]
  exact (boundedTermsSingle_coarse_KMap_apply P 0 k x.2).symm

variable [(abelianExactStructure A).IsKernelClosed P]

/-- The proved actual global unique factorization makes the original product homomorphism bijective.
-/
theorem boundedTermsAcyclicSingleKMap_bijective (k : ℕ) :
    Function.Bijective (boundedTermsAcyclicSingleKMap P k) := by
  constructor
  · intro x y hxy
    exact (boundedTerms_existsUnique_acyclic_single_zero P k (boundedTermsAcyclicSingleKMap P k
        x)).unique
      rfl hxy.symm
  · intro x
    obtain ⟨p, hp, _⟩ := boundedTerms_existsUnique_acyclic_single_zero P k x
    exact ⟨p, hp⟩

/-- The genuine fine K-group is the product of the actual acyclic K-group
and the original term K-group, with the original product map as its forward map. -/
def boundedTermsAcyclicSingleKEquiv (k : ℕ) :
    ((ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) ≃*
        (ofExactCategory (boundedTermsExactStructure P)).K k :=
  MulEquiv.ofBijective (boundedTermsAcyclicSingleKMap P k)
      (boundedTermsAcyclicSingleKMap_bijective P k)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem boundedTermsAcyclicSingleKEquiv_coe (k : ℕ) :
    MonoidHomClass.toMonoidHom (boundedTermsAcyclicSingleKEquiv P k) =
        boundedTermsAcyclicSingleKMap P k := rfl


/-- The forward map is literally the product of the two original public KMaps. -/
@[simp] theorem boundedTermsAcyclicSingleKEquiv_apply (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    boundedTermsAcyclicSingleKEquiv P k x =
      KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k x.1 *
        KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k x.2 := rfl

/-- Its inverse is characterized by the actual original factorization. -/
theorem boundedTermsAcyclicSingleKEquiv_symm_spec (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k
        ((boundedTermsAcyclicSingleKEquiv P k).symm x).1 *
      KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k
        ((boundedTermsAcyclicSingleKEquiv P k).symm x).2 = x :=
  (boundedTermsAcyclicSingleKEquiv P k).apply_symm_apply x

/-- Changing weak equivalences is the original coarse single map after the second projection. -/
theorem boundedTermsAcyclicSingleKEquiv_coarse (k : ℕ) :
    (KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k).comp
      (boundedTermsAcyclicSingleKEquiv P k).toMonoidHom =
        (KMap (boundedTermsSingle_coarseExact P 0) k).comp (MonoidHom.snd _ _) := by
  ext x
  exact boundedTermsAcyclicSingleKMap_coarse P k x

end CategoryTheory.Waldhausen.GilletWaldhausen

namespace CategoryTheory.Waldhausen.GilletWaldhausen

attribute [colib_tag "COL-0257",
  colib_ref "WeibelKBook" "V, proof of Theorem 2.2, pp. 13-14" "adaptation"
    "Actual acyclic-times-single decomposition of bounded complexes with isomorphism weak maps"]
  boundedTermsAcyclicSingleKEquiv
  boundedTermsAcyclicSingleKEquiv_apply
  boundedTermsAcyclicSingleKEquiv_coarse

end CategoryTheory.Waldhausen.GilletWaldhausen
