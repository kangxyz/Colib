/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectionTranslations
public import Colib.Topology.LocalCoefficients.HomotopySquare
public import Colib.Topology.LocalCoefficients.Abelian

/-!
Adapted from `Quillen/Topology/LocalCoefficients/ProjectionTranslations.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps retained.

# Abelian local homology of the original first-projection comma transitions -/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace CategoryTheory.GroupCompletion.Localization
open FundamentalGroupoid.LocalCoefficients
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
  [∀ A : C, (tensorRight A).Faithful]
  {D : Type (max u v)} [Category.{max u v} D] [MonoidalLeftAction C D]

/-- The actual representative-level comma transition inherits its abelian local
homology isomorphism from the original translation, via the specified adjunctions. -/
theorem isIso_commaTransition_abelianHomology_of_action
    (ha : ∀ (s : C) (A : System.{max u v, max u v} (ClassifyingSpace D)),
      AbelianMonodromy A → ∀ n : ℕ,
        IsIso (pushforwardHomologyMap
          (classifyingSpaceMapUniversal (MonoidalLeftAction.actionLeft D s)) A n))
    {X Y : ActionLocalization C C} (f : X ⟶ Y)
    (A : System.{max u v, max u v}
      (ClassifyingSpace (CostructuredArrow (projection (D := D)) Y)))
    (hA : AbelianMonodromy A) (n : ℕ) :
    IsIso (pushforwardHomologyMap (classifyingSpaceMapUniversal
      (CostructuredArrow.map (S := projection (D := D)) f)) A n) := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj f
  apply isIso_pushforwardHomologyMap_of_homotopySquare
    (commaEntryClassifyingHomotopyEquiv X.obj)
    (commaEntryClassifyingHomotopyEquiv Y.obj)
    (classifyingSpaceMapUniversal (MonoidalLeftAction.actionLeft D r.denom)) _
    (commaTranslationHomotopy r.denom r.map) A n
  exact ha r.denom _ (pullback_abelianMonodromy _ hA) n

end CategoryTheory.GroupCompletion.Localization
