/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Waldhausen.GilletWaldhausen.BoundedTermsBasedStrata
public import Colib.Topology.FilteredRealization.BasedGroups

/-! # Actual finite-stage coverage and equality detection for bounded-term K-groups

The proved simplicial filtered colimit and compact based-cube factorization
apply to the strictly compatible tagged-zero models. Exact identity functors
then transport their conclusions to the original canonical KMaps of the
original inherited isomorphism models. No categorywide uniform bound,
transition equivalence, or injectivity of realization maps is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/BoundedTermsKCoverage.lean` at Quillen commit
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
open scoped Simplicial
universe v u
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual original raw S-inclusion sends the tagged chosen point exactly. -/
theorem boundedTermsBasedInclusion_basepoint (N : ℕ) :
    SSet.toTop.map (boundedTermsStratumSSetInclusion P (MorphismProperty.isomorphisms _) N)
      (boundedTermsBasedStructure P N).kBasepoint =
        (ofExactCategory (boundedTermsExactStructure P)).kBasepoint :=
  deloopingMap_basepoint_of_zeroEq (boundedTermsBasedInclusionExact P N) rfl

/-- The actual original transition retains the chosen stage points exactly. -/
theorem boundedTermsBasedTransition_basepoint {N M : ℕ} (h : N ≤ M) :
    SSet.toTop.map (boundedTermsStratumSSetTransition P (MorphismProperty.isomorphisms _) h)
      (boundedTermsBasedStructure P N).kBasepoint = (boundedTermsBasedStructure P M).kBasepoint :=
  deloopingMap_basepoint_of_zeroEq (boundedTermsBasedTransitionExact P h) rfl

/-- Every actual bounded-term K-class is the image of an original finite-stratum K-class. -/
theorem boundedTerms_KMap_jointlySurjective (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    ∃ N : ℕ, ∃ y : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k,
      KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y = x := by
  obtain ⟨j, y, hy⟩ := FilteredRealization.piMap_jointlySurjective
    (boundedTermsSSetDiagram P (MorphismProperty.isomorphisms _))
    (boundedTermsSSetCocone P (MorphismProperty.isomorphisms _))
    (boundedTermsSSetCoconeIsColimit P (MorphismProperty.isomorphisms _))
    (fun j ↦ (boundedTermsBasedStructure P (boundedStageRank j)).kBasepoint)
    (ofExactCategory (boundedTermsExactStructure P)).kBasepoint
    (fun {_ _} f ↦ boundedTermsBasedTransition_basepoint P (leOfHom (AsSmall.down.map f)))
    (fun j ↦ boundedTermsBasedInclusion_basepoint P (boundedStageRank j)) k x
  refine ⟨boundedStageRank j, KMap (boundedTermsBasedToOriginalExact P (boundedStageRank j)) k
    y, ?_⟩
  rw [boundedTermsBasedInclusion_KMap, KMap_eq_piMap_of_zeroEq
    (boundedTermsBasedInclusionExact P (boundedStageRank j)) rfl k]
  exact hy

/-- Equality under an original stage KMap is detected by an original later transition KMap. -/
theorem boundedTerms_KMap_eq_eventually (N k : ℕ)
    (x y : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k)
    (he : KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x =
      KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y) :
    ∃ M : ℕ, ∃ h : N ≤ M,
      KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k x =
        KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k y := by
  let x' := KMap (boundedTermsOriginalToBasedExact P N) k x
  let y' := KMap (boundedTermsOriginalToBasedExact P N) k y
  have he' : HomotopyGroup.piMap k
      (SSet.toTop.map (boundedTermsStratumSSetInclusion P (MorphismProperty.isomorphisms _) N)).hom
      (boundedTermsBasedInclusion_basepoint P N) x' = HomotopyGroup.piMap k
      (SSet.toTop.map (boundedTermsStratumSSetInclusion P (MorphismProperty.isomorphisms _) N)).hom
      (boundedTermsBasedInclusion_basepoint P N) y' := by
    have hx := DFunLike.congr_fun
      (KMap_eq_piMap_of_zeroEq (boundedTermsBasedInclusionExact P N) rfl k) x'
    have hy := DFunLike.congr_fun
      (KMap_eq_piMap_of_zeroEq (boundedTermsBasedInclusionExact P N) rfl k) y'
    exact hx.symm.trans ((boundedTermsOriginalInclusion_KMap P N k x).trans
      ((he.trans (boundedTermsOriginalInclusion_KMap P N k y).symm).trans hy))
  obtain ⟨j, f, hf⟩ := FilteredRealization.piMap_eq_eventually
    (boundedTermsSSetDiagram P (MorphismProperty.isomorphisms _))
    (boundedTermsSSetCocone P (MorphismProperty.isomorphisms _))
    (boundedTermsSSetCoconeIsColimit P (MorphismProperty.isomorphisms _))
    (fun j ↦ (boundedTermsBasedStructure P (boundedStageRank j)).kBasepoint)
    (ofExactCategory (boundedTermsExactStructure P)).kBasepoint
    (fun {_ _} f ↦ boundedTermsBasedTransition_basepoint P (leOfHom (AsSmall.down.map f)))
    (fun j ↦ boundedTermsBasedInclusion_basepoint P (boundedStageRank j))
    (boundedStageIndex N) k x' y' he'
  let h : N ≤ boundedStageRank j := leOfHom (AsSmall.down.map f)
  have hf' : KMap (boundedTermsBasedTransitionExact P h) k x' =
      KMap (boundedTermsBasedTransitionExact P h) k y' := by
    rw [KMap_eq_piMap_of_zeroEq (boundedTermsBasedTransitionExact P h) rfl k]
    exact hf
  have hh := congrArg (KMap (boundedTermsBasedToOriginalExact P (boundedStageRank j)) k) hf'
  rw [← boundedTermsBasedTransition_KMap, ← boundedTermsBasedTransition_KMap] at hh
  change KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k
      (KMap (boundedTermsBasedToOriginalExact P N) k
        (KMap (boundedTermsOriginalToBasedExact P N) k x)) =
    KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k
      (KMap (boundedTermsBasedToOriginalExact P N) k
        (KMap (boundedTermsOriginalToBasedExact P N) k y)) at hh
  rw [boundedTermsOriginalBased_KMap_inv, boundedTermsOriginalBased_KMap_inv] at hh
  exact ⟨boundedStageRank j, h, hh⟩

/-- An actual stage class vanishing globally vanishes under an actual later original KMap. -/
theorem boundedTerms_KMap_eq_one_eventually (N k : ℕ)
    (x : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k)
    (he : KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x = 1) :
    ∃ M : ℕ, ∃ h : N ≤ M, KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k x = 1
      := by
  obtain ⟨M, h, hh⟩ := boundedTerms_KMap_eq_eventually P N k x 1 (he.trans (map_one _).symm)
  exact ⟨M, h, hh.trans (map_one _)⟩

end CategoryTheory.Waldhausen.GilletWaldhausen
