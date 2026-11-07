/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.BoundedSSet
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The genuine filtered simplicial union of bounded acyclic strata

The actual S-construction is the filtered colimit of its symmetric term-bound
strata. The generic filtered-realization API is used directly by the later based
K-group coverage proof. No global bound or stage equivalence is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/BoundedSSetColimit.lean` at Quillen commit
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
variable (w : MorphismProperty (boundedAcyclic P).FullSubcategory)

/-- A universe-compatible copy of the natural-number indexing category. -/
abbrev BoundedStageIndex := AsSmall.{u} ℕ

/-- The actual symmetric term bound at this stage. -/
abbrev boundedStageRank (j : BoundedStageIndex.{u}) : ℕ := AsSmall.down.obj j

/-- A concrete natural-number bound as a stage index. -/
abbrev boundedStageIndex (N : ℕ) : BoundedStageIndex.{u} := AsSmall.up.obj N

/-- The strict increasing diagram of actual bounded S-sets. -/
@[implicit_reducible]
def boundedSSetDiagram : BoundedStageIndex.{max u v} ⥤ SSet.{max u v} where
  obj j := boundedStratumSSet P w (boundedStageRank j)
  map f := boundedStratumSSetTransition P w (leOfHom (AsSmall.down.map f))
  map_id _ := boundedStratumSSetTransition_id P w _
  map_comp _ _ := (boundedStratumSSetTransition_comp P w _ _).symm

/-- Its actual canonical cocone into the original bounded-acyclic S-set. -/
@[implicit_reducible]
def boundedSSetCocone : Cocone (boundedSSetDiagram P w) where
  pt := boundedAcyclicSSet P w
  ι :=
    { app j := boundedStratumSSetInclusion P w (boundedStageRank j)
      naturality {j k} f := by
        change boundedStratumSSetTransition P w (leOfHom (AsSmall.down.map f)) ≫
          boundedStratumSSetInclusion P w (boundedStageRank k) =
            boundedStratumSSetInclusion P w (boundedStageRank j) ≫ 𝟙 _
        rw [Category.comp_id]
        exact boundedStratumSSetTransition_inclusion P w (leOfHom (AsSmall.down.map f)) }

/-- The original S-set is genuinely the filtered colimit of its actual
bounded strata, proved degreewise from finite-grid coverage and injectivity. -/
def boundedSSetCoconeIsColimit : IsColimit (boundedSSetCocone P w) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply Types.FilteredColimit.isColimitOf'
  · intro F
    obtain ⟨N, G, hG⟩ := boundedStratumSSetInclusion_surjective P w n F
    exact ⟨boundedStageIndex N, G, hG.symm⟩
  · intro j F G h
    have hFG := boundedStratumSSetInclusion_injective P w (boundedStageRank j) n h
    exact ⟨j, 𝟙 j, congrArg (((boundedSSetDiagram P w).map (𝟙 j)).app n) hFG⟩

end CategoryTheory.Waldhausen.GilletWaldhausen
