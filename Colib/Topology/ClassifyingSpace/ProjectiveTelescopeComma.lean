/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeAbelianHomology
public import Colib.CategoryTheory.Monoidal.TranslationTelescopeAction
public import Colib.Topology.LocalCoefficients.ProjectionTranslations
public import Colib.CategoryTheory.TheoremA.ReplacementEntry
public import Colib.CategoryTheory.GroupCompletion.UnitEntry

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveTelescopeComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps retained.

# Actual projective telescope action and first-projection comma transport -/

@[expose] public section

open CategoryTheory.GroupCompletion
open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory MonoidalCategory
universe u
namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open FundamentalGroupoid.LocalCoefficients GroupCompletion
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
variable (R : Type u) [Ring R]

/-- The genuine original left action on the right-free-rank-one telescope. -/
@[instance_reducible]
def projectiveTelescopeAction : MonoidalLeftAction (IsoCategory Rᵐᵒᵖ) (ProjectiveTelescope R) :=
  TranslationTelescope.monoidalLeftAction (freeIso Rᵐᵒᵖ 1)

attribute [local instance] projectiveTelescopeAction

/-- This localization uses the original telescope and its actual monoidal action. -/
abbrev ProjectiveTelescopeLocalization := Localization (IsoCategory Rᵐᵒᵖ) (ProjectiveTelescope R)

/-- The original first-coordinate projection, before any homology-fibration assertion. -/
def projectiveTelescopeProjection : ProjectiveTelescopeLocalization R ⥤
    ActionLocalization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ) :=
  Localization.projection

/-- Every actual comma transition preserves abelian local homology. The proof
uses the original action theorem and the actual comma-entry adjunction square. -/
theorem projectiveTelescopeProjection_comma_abelianHomology_isIso
    {X Y : ActionLocalization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ)} (f : X ⟶ Y)
    (A : System.{u + 1, u + 1}
      (ClassifyingSpace (CostructuredArrow (projectiveTelescopeProjection R) Y)))
    (hA : AbelianMonodromy A) (n : ℕ) :
    IsIso (pushforwardHomologyMap (classifyingSpaceMapUniversal
      (CostructuredArrow.map (S := projectiveTelescopeProjection R) f)) A n) := by
  let : ∀ P : IsoCategory Rᵐᵒᵖ, (tensorRight P).Faithful := directSumRight_faithful Rᵐᵒᵖ
  apply Localization.isIso_commaTransition_abelianHomology_of_action _ f A hA n
  intro P B hB d
  rw [classifyingSpaceMapUniversal_eq]
  exact projectiveTelescopeTranslation_abelianHomology_isIso R P B hB d

/-- The canonical ordinary comma diagram is strictly functorial. -/
def projectiveTelescopeCommaDiagram :
    ActionLocalization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ) ⥤ SSet.{u + 1} :=
  TheoremA.commaNerveDiagram (projectiveTelescopeProjection R)

/-- Every actual diagram arrow is an abelian local homology isomorphism. -/
theorem projectiveTelescopeCommaDiagram_map_abelianHomology_isIso
    {X Y : ActionLocalization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ)} (f : X ⟶ Y)
    (A : System.{u + 1, u + 1}
      (ClassifyingSpace (CostructuredArrow (projectiveTelescopeProjection R) Y)))
    (hA : AbelianMonodromy A) (n : ℕ) :
    IsIso (pushforwardHomologyMap
      (SSet.toTop.map ((projectiveTelescopeCommaDiagram R).map f)).hom A n) := by
  have h := projectiveTelescopeProjection_comma_abelianHomology_isIso R f A hA n
  rw [classifyingSpaceMapUniversal_eq] at h
  exact h

/-- The strict simplicial replacement uses the original comma diagram, without
any monoidal strictification or replacement of the telescope. -/
def projectiveTelescopeCommaReplacement : SimplexCategoryᵒᵖ ⥤ SSet.{u + 1} :=
  TheoremA.simplicialReplacement (projectiveTelescopeCommaDiagram R)

/-- Every outer simplicial operator transports its coefficient component along
an actual first-vertex comma arrow, which preserves abelian local homology. -/
theorem projectiveTelescopeCommaReplacement_transport_isIso
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    (σ : (nerve (ActionLocalization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ))).obj p)
    (A : System.{u + 1, u + 1}
      (ClassifyingSpace (CostructuredArrow (projectiveTelescopeProjection R)
        (((nerve (ActionLocalization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ))).map α σ).obj 0))))
    (hA : AbelianMonodromy A) (n : ℕ) :
    IsIso (pushforwardHomologyMap
      (SSet.toTop.map ((projectiveTelescopeCommaDiagram R).map
        (TheoremA.firstVertexEdge α σ))).hom A n) :=
  projectiveTelescopeCommaDiagram_map_abelianHomology_isIso R
    (TheoremA.firstVertexEdge α σ) A hA n


/-- The original telescope enters the strict comma replacement at the actual unit. -/
def projectiveTelescopeReplacementEntry : nerve (ProjectiveTelescope R) ⟶
    TheoremA.replacementDiagonal (projectiveTelescopeCommaDiagram R) :=
  nerveMap (Localization.commaEntry (D := ProjectiveTelescope R) (𝟙_ (IsoCategory Rᵐᵒᵖ))) ≫
    TheoremA.replacementEntry (projectiveTelescopeCommaDiagram R) ⟨𝟙_ (IsoCategory Rᵐᵒᵖ)⟩

/-- The source augmentation sends this specified entry to exactly the original
unit-denominator functor, rather than to an unspecified equivalent map. -/
theorem projectiveTelescopeReplacementEntry_source :
    projectiveTelescopeReplacementEntry R ≫
      TheoremA.diagonalSourceMap (projectiveTelescopeProjection R) =
      nerveMap (Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := ProjectiveTelescope R)) := by
  unfold projectiveTelescopeReplacementEntry
  erw [Category.assoc]
  change nerveMap _ ≫
    (TheoremA.replacementEntry (TheoremA.commaNerveDiagram (projectiveTelescopeProjection R)) _ ≫
      TheoremA.diagonalSourceMap _) = _
  rw [TheoremA.replacementEntry_diagonalSourceMap]
  rfl


end ModuleCat.FiniteProjective
