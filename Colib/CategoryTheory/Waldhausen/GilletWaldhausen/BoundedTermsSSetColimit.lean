/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.BoundedTermsSSet
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.BoundedSSetColimit

/-! # The actual filtered simplicial union of bounded termwise strata

Finite-grid coverage and injectivity prove the actual simplicial colimit.
The later based K-group coverage proof applies the generic filtered-realization
API directly to this colimit. No global bound or stage equivalence is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/BoundedTermsSSetColimit.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section


open CategoryTheory.ExactCategory
open CochainComplex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u w
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
variable (w : MorphismProperty (boundedTerms P).FullSubcategory)

/-- The strict increasing diagram of actual bounded S-sets. -/
@[implicit_reducible]
def boundedTermsSSetDiagram : BoundedStageIndex.{max u v} ⥤ SSet.{max u v} where
  obj j := boundedTermsStratumSSet P w (boundedStageRank j)
  map f := boundedTermsStratumSSetTransition P w (leOfHom (AsSmall.down.map f))
  map_id _ := boundedTermsStratumSSetTransition_id P w _
  map_comp _ _ := (boundedTermsStratumSSetTransition_comp P w _ _).symm

/-- Its actual canonical cocone into the original bounded-term S-set. -/
@[implicit_reducible]
def boundedTermsSSetCocone : Cocone (boundedTermsSSetDiagram P w) where
  pt := boundedTermsSSet P w
  ι :=
    { app j := boundedTermsStratumSSetInclusion P w (boundedStageRank j)
      naturality {j k} f := by
        change boundedTermsStratumSSetTransition P w (leOfHom (AsSmall.down.map f)) ≫
          boundedTermsStratumSSetInclusion P w (boundedStageRank k) =
            boundedTermsStratumSSetInclusion P w (boundedStageRank j) ≫ 𝟙 _
        rw [Category.comp_id]
        exact boundedTermsStratumSSetTransition_inclusion P w (leOfHom (AsSmall.down.map f)) }

/-- The original S-set is genuinely the filtered colimit of its actual
bounded strata, proved degreewise from finite-grid coverage and injectivity. -/
def boundedTermsSSetCoconeIsColimit : IsColimit (boundedTermsSSetCocone P w) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply Types.FilteredColimit.isColimitOf'
  · intro F
    obtain ⟨N, G, hG⟩ := boundedTermsStratumSSetInclusion_surjective P w n F
    exact ⟨boundedStageIndex N, G, hG.symm⟩
  · intro j F G h
    have hFG := boundedTermsStratumSSetInclusion_injective P w (boundedStageRank j) n h
    exact ⟨j, 𝟙 j, congrArg (((boundedTermsSSetDiagram P w).map (𝟙 j)).app n) hFG⟩

end CategoryTheory.Waldhausen.GilletWaldhausen
