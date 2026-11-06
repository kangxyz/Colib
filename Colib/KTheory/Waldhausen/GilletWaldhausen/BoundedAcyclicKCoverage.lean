/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Waldhausen.GilletWaldhausen.BoundedAcyclicBasedStrata
public import Colib.Topology.FilteredRealization.BasedGroups

/-! # Actual finite-stage coverage and equality detection for bounded-acyclic K-groups

The proved simplicial filtered colimit and compact based-cube factorization
apply to the strictly compatible tagged-zero models. Exact identity functors
then transport their conclusions to the original canonical KMaps of the
original inherited isomorphism models. No categorywide uniform bound,
transition equivalence, or injectivity of realization maps is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/BoundedAcyclicKCoverage.lean` at Quillen commit
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
theorem boundedAcyclicBasedInclusion_basepoint (N : ℕ) :
    SSet.toTop.map (boundedStratumSSetInclusion P (MorphismProperty.isomorphisms _) N)
      (boundedAcyclicBasedStructure P N).kBasepoint =
        (ofExactCategory (boundedAcyclicExactStructure P)).kBasepoint :=
  deloopingMap_basepoint_of_zeroEq (boundedAcyclicBasedInclusionExact P N) rfl

/-- The actual original transition retains the chosen stage points exactly. -/
theorem boundedAcyclicBasedTransition_basepoint {N M : ℕ} (h : N ≤ M) :
    SSet.toTop.map (boundedStratumSSetTransition P (MorphismProperty.isomorphisms _) h)
      (boundedAcyclicBasedStructure P N).kBasepoint = (boundedAcyclicBasedStructure P
        M).kBasepoint :=
  deloopingMap_basepoint_of_zeroEq (boundedAcyclicBasedTransitionExact P h) rfl

/-- Every actual bounded-acyclic K-class is the image of an original finite-stratum K-class. -/
theorem boundedAcyclic_KMap_jointlySurjective (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k) :
    ∃ N : ℕ, ∃ y : (ofExactCategory (boundedStratumExactStructure P N)).K k,
      KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y = x := by
  obtain ⟨j, y, hy⟩ := FilteredRealization.piMap_jointlySurjective
    (boundedSSetDiagram P (MorphismProperty.isomorphisms _))
    (boundedSSetCocone P (MorphismProperty.isomorphisms _))
    (boundedSSetCoconeIsColimit P (MorphismProperty.isomorphisms _))
    (fun j ↦ (boundedAcyclicBasedStructure P (boundedStageRank j)).kBasepoint)
    (ofExactCategory (boundedAcyclicExactStructure P)).kBasepoint
    (fun {_ _} f ↦ boundedAcyclicBasedTransition_basepoint P (leOfHom (AsSmall.down.map f)))
    (fun j ↦ boundedAcyclicBasedInclusion_basepoint P (boundedStageRank j)) k x
  refine ⟨boundedStageRank j, KMap (boundedAcyclicBasedToOriginalExact P (boundedStageRank j)) k
    y, ?_⟩
  rw [boundedAcyclicBasedInclusion_KMap, KMap_eq_piMap_of_zeroEq
    (boundedAcyclicBasedInclusionExact P (boundedStageRank j)) rfl k]
  exact hy

/-- Equality under an original stage KMap is detected by an original later transition KMap. -/
theorem boundedAcyclic_KMap_eq_eventually (N k : ℕ)
    (x y : (ofExactCategory (boundedStratumExactStructure P N)).K k)
    (he : KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x =
      KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y) :
    ∃ M : ℕ, ∃ h : N ≤ M,
      KMap (boundedStratumTransitionExact P h).waldhausenExact k x =
        KMap (boundedStratumTransitionExact P h).waldhausenExact k y := by
  let x' := KMap (boundedAcyclicOriginalToBasedExact P N) k x
  let y' := KMap (boundedAcyclicOriginalToBasedExact P N) k y
  have he' : HomotopyGroup.piMap k
      (SSet.toTop.map (boundedStratumSSetInclusion P (MorphismProperty.isomorphisms _) N)).hom
      (boundedAcyclicBasedInclusion_basepoint P N) x' = HomotopyGroup.piMap k
      (SSet.toTop.map (boundedStratumSSetInclusion P (MorphismProperty.isomorphisms _) N)).hom
      (boundedAcyclicBasedInclusion_basepoint P N) y' := by
    have hx := DFunLike.congr_fun
      (KMap_eq_piMap_of_zeroEq (boundedAcyclicBasedInclusionExact P N) rfl k) x'
    have hy := DFunLike.congr_fun
      (KMap_eq_piMap_of_zeroEq (boundedAcyclicBasedInclusionExact P N) rfl k) y'
    exact hx.symm.trans ((boundedAcyclicOriginalInclusion_KMap P N k x).trans
      ((he.trans (boundedAcyclicOriginalInclusion_KMap P N k y).symm).trans hy))
  obtain ⟨j, f, hf⟩ := FilteredRealization.piMap_eq_eventually
    (boundedSSetDiagram P (MorphismProperty.isomorphisms _))
    (boundedSSetCocone P (MorphismProperty.isomorphisms _))
    (boundedSSetCoconeIsColimit P (MorphismProperty.isomorphisms _))
    (fun j ↦ (boundedAcyclicBasedStructure P (boundedStageRank j)).kBasepoint)
    (ofExactCategory (boundedAcyclicExactStructure P)).kBasepoint
    (fun {_ _} f ↦ boundedAcyclicBasedTransition_basepoint P (leOfHom (AsSmall.down.map f)))
    (fun j ↦ boundedAcyclicBasedInclusion_basepoint P (boundedStageRank j))
    (boundedStageIndex N) k x' y' he'
  let h : N ≤ boundedStageRank j := leOfHom (AsSmall.down.map f)
  have hf' : KMap (boundedAcyclicBasedTransitionExact P h) k x' =
      KMap (boundedAcyclicBasedTransitionExact P h) k y' := by
    rw [KMap_eq_piMap_of_zeroEq (boundedAcyclicBasedTransitionExact P h) rfl k]
    exact hf
  have hh := congrArg (KMap (boundedAcyclicBasedToOriginalExact P (boundedStageRank j)) k) hf'
  rw [← boundedAcyclicBasedTransition_KMap, ← boundedAcyclicBasedTransition_KMap] at hh
  change KMap (boundedStratumTransitionExact P h).waldhausenExact k
      (KMap (boundedAcyclicBasedToOriginalExact P N) k
        (KMap (boundedAcyclicOriginalToBasedExact P N) k x)) =
    KMap (boundedStratumTransitionExact P h).waldhausenExact k
      (KMap (boundedAcyclicBasedToOriginalExact P N) k
        (KMap (boundedAcyclicOriginalToBasedExact P N) k y)) at hh
  rw [boundedAcyclicOriginalBased_KMap_inv, boundedAcyclicOriginalBased_KMap_inv] at hh
  exact ⟨boundedStageRank j, h, hh⟩

/-- An actual stage class vanishing globally vanishes under an actual later original KMap. -/
theorem boundedAcyclic_KMap_eq_one_eventually (N k : ℕ)
    (x : (ofExactCategory (boundedStratumExactStructure P N)).K k)
    (he : KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x = 1) :
    ∃ M : ℕ, ∃ h : N ≤ M, KMap (boundedStratumTransitionExact P h).waldhausenExact k x = 1 := by
  obtain ⟨M, h, hh⟩ := boundedAcyclic_KMap_eq_eventually P N k x 1 (he.trans (map_one _).symm)
  exact ⟨M, h, hh.trans (map_one _)⟩

end CategoryTheory.Waldhausen.GilletWaldhausen
