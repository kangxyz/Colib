/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.PathComponent
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
Adapted from `Quillen/Topology/FundamentalGroupoid/PathComponent.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Colib objects.

# The actual fundamental groupoid of a path component

Component inclusion is fully faithful: paths and endpoint-fixed homotopies
restrict to the component without requiring it to be open. Its image is exactly
the full subgroupoid of ambient points in the original path component.
-/

@[expose] public section
noncomputable section
open Topology CategoryTheory
universe u
namespace FundamentalGroupoid.Component
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {Y : Type u} [TopologicalSpace Y] (y : Y)

/-- The actual continuous inclusion of the path-component subspace. -/
def inclusion : C(pathComponent y, Y) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The original inclusion-induced functor on fundamental groupoids. -/
def inclusionMap : FundamentalGroupoid (pathComponent y) ⥤ FundamentalGroupoid Y :=
  FundamentalGroupoid.map (inclusion y)

/-- Paths and endpoint-fixed homotopies give a bijection on each original hom set. -/
lemma inclusionMap_bijective (a b : FundamentalGroupoid (pathComponent y)) :
    Function.Bijective ((inclusionMap y).map :
      (a ⟶ b) → ((inclusionMap y).obj a ⟶ (inclusionMap y).obj b)) := by
  constructor
  · intro p q h
    induction p using Path.Homotopic.Quotient.ind with | mk p =>
    induction q using Path.Homotopic.Quotient.ind with | mk q =>
    obtain ⟨H⟩ := Path.Homotopic.Quotient.exact h
    exact Quotient.sound ⟨pathComponentHomotopy H⟩
  · intro p
    induction p using Path.Homotopic.Quotient.ind with | mk p =>
    change Path a.as.val b.as.val at p
    refine ⟨Path.Homotopic.Quotient.mk (pathComponentPath p), ?_⟩
    change Path.Homotopic.Quotient.mk
      ((pathComponentPath p).map continuous_subtype_val) = _
    rw [pathComponentPath_map]

/-- Component inclusion reflects equality of the original path classes. -/
instance inclusionMap_faithful : (inclusionMap y).Faithful where
  map_injective h := (inclusionMap_bijective y _ _).injective h

/-- Every ambient path between component points has its actual restricted path class. -/
instance inclusionMap_full : (inclusionMap y).Full where
  map_surjective := (inclusionMap_bijective y _ _).surjective

/-- The unique morphism preimage is the class of the actual restricted path. -/
lemma inclusionMap_preimage_path {a b : pathComponent y} (p : Path a.val b.val) :
    (inclusionMap y).preimage (X := FundamentalGroupoid.mk a) (Y := FundamentalGroupoid.mk b)
      (Path.Homotopic.Quotient.mk p) =
        Path.Homotopic.Quotient.mk (pathComponentPath p) := by
  apply (inclusionMap y).map_injective
  rw [Functor.map_preimage]
  change Path.Homotopic.Quotient.mk p =
    Path.Homotopic.Quotient.mk ((pathComponentPath p).map continuous_subtype_val)
  rw [pathComponentPath_map]

/-- The original component is saturated under every actual fundamental-groupoid arrow. -/
lemma mem_of_hom {a b : FundamentalGroupoid Y} (f : a ⟶ b)
    (ha : a.as ∈ pathComponent y) : b.as ∈ pathComponent y := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
  exact (show Joined a.as b.as from ⟨p⟩).mem_pathComponent ha

/-- The property of lying in the original path component. -/
def componentProperty : ObjectProperty (FundamentalGroupoid Y) :=
  fun a => a.as ∈ pathComponent y

/-- The original inclusion, with codomain restricted to its full ambient subgroupoid. -/
def toFullSubcategory : FundamentalGroupoid (pathComponent y) ⥤
    (componentProperty y).FullSubcategory :=
  (componentProperty y).lift (inclusionMap y) (fun a => a.as.property)

/-- The lifted original inclusion remains fully faithful. -/
instance toFullSubcategory_full : (toFullSubcategory y).Full := by
  dsimp only [toFullSubcategory]
  infer_instance

/-- The lifted original inclusion reflects all path classes. -/
instance toFullSubcategory_faithful : (toFullSubcategory y).Faithful := by
  dsimp only [toFullSubcategory]
  infer_instance

/-- Each original ambient point in the component is literally in the image. -/
instance toFullSubcategory_essSurj : (toFullSubcategory y).EssSurj := by
  apply Functor.essSurj_of_surj
  intro a
  refine ⟨FundamentalGroupoid.mk ⟨a.obj.as, a.property⟩, ?_⟩
  cases a with
  | mk a ha => cases a; rfl

/-- The component's fundamental groupoid is equivalent to the full ambient subgroupoid. -/
instance toFullSubcategory_isEquivalence : (toFullSubcategory y).IsEquivalence where

/-- The equivalence retains the original inclusion on every path class. -/
def equivalence : FundamentalGroupoid (pathComponent y) ≌
    (componentProperty y).FullSubcategory :=
  (toFullSubcategory y).asEquivalence

/-- Forgetting the component restriction recovers the original induced inclusion functor. -/
lemma equivalence_forward :
    (equivalence y).functor ⋙ (componentProperty y).ι = inclusionMap y := rfl

end FundamentalGroupoid.Component
