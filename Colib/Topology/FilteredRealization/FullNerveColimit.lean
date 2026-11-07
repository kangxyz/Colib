/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.FilteredRealization.NerveColimit

/-!
# Filtered nerve colimits from full stage inclusions

For a filtered categorical cocone with full stage legs, joint lifting of
objects already supplies joint lifting of arrows: move both endpoints to a
common stage and use fullness there. Faithfulness and eventual object equality
then give the actual simplicial colimit. Injective stage object maps are a
sufficient condition for the latter equality requirement.

These criteria are used by the finite-support Q-stage construction. They do
not assert that an unspecified categorical diagram or its basepoints exist.

Implementation provenance:
`Quillen/Topology/FilteredRealization/FullNerveColimit.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual objects, maps, degrees
and universe parameters are retained.
-/
@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FilteredNerveColimit

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ Cat.{u, u}) (c : Cocone F)

/-- Full stage legs reduce joint arrow lifting to joint object lifting. -/
theorem arrowSurjective_of_full [∀ j, (leg F c j).Full]
    (ho : ∀ X : c.pt, ∃ (j : J) (x : F.obj j), (leg F c j).obj x = X) :
    ArrowSurjective F c := by
  intro X Y f
  obtain ⟨j, x, hx⟩ := ho X
  obtain ⟨k, y, hy⟩ := ho Y
  let l := IsFiltered.max j k
  let a : j ⟶ l := IsFiltered.leftToMax j k
  let b : k ⟶ l := IsFiltered.rightToMax j k
  let x' := (step F a).obj x
  let y' := (step F b).obj y
  have hx' : (leg F c l).obj x' = X := (leg_step_obj F c a x).trans hx
  have hy' : (leg F c l).obj y' = Y := (leg_step_obj F c b y).trans hy
  let g := (leg F c l).preimage (eqToHom hx' ≫ f ≫ eqToHom hy'.symm)
  refine ⟨l, x', y', g, hx', hy', ?_⟩
  simp [g]

/-- Full faithful stages cover the target nerve once objects cover it and
object equality is detected after a transition. -/
def nerveCoconeIsColimitOfFull [∀ j, (leg F c j).Full]
    [∀ j, (leg F c j).Faithful]
    (ho : ∀ X : c.pt, ∃ (j : J) (x : F.obj j), (leg F c j).obj x = X)
    (he : EventuallyEqualObjects F c) : IsColimit (nerveFunctor.mapCocone c) :=
  nerveCoconeIsColimit F c ho (arrowSurjective_of_full F c ho) he

omit [IsFiltered J] in
/-- Injective stage object maps imply the required eventual object equality. -/
theorem eventuallyEqualObjects_of_injective
    (hi : ∀ j, Function.Injective (leg F c j).obj) : EventuallyEqualObjects F c := by
  intro j x y h
  refine ⟨j, 𝟙 j, ?_⟩
  exact congrArg (step F (𝟙 j)).obj (hi j h)

/-- Full faithful stage inclusions injective on objects give a nerve colimit
from joint object surjectivity alone. -/
def nerveCoconeIsColimitOfFullOfInjective [∀ j, (leg F c j).Full]
    [∀ j, (leg F c j).Faithful]
    (ho : ∀ X : c.pt, ∃ (j : J) (x : F.obj j), (leg F c j).obj x = X)
    (hi : ∀ j, Function.Injective (leg F c j).obj) :
    IsColimit (nerveFunctor.mapCocone c) :=
  nerveCoconeIsColimitOfFull F c ho (eventuallyEqualObjects_of_injective F c hi)

end CategoryTheory.FilteredNerveColimit
