/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.MonomorphismHEP
public import Colib.Topology.Homotopy.Equiv.IsoSquare
public import Colib.Topology.Pushout.HomotopyEquivalence
public import Colib.Topology.Realization.LocallyCompactProduct

/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/MapEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native simplicial objects,
realization maps and full proof are retained. -/

/-!
# Homotopy equivalence of a prescribed simplicial realization map -/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet

/-- The specified realized simplicial map is the forward map of an actual
homotopy equivalence. -/
def IsRealizationEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∃ e : ContinuousMap.HomotopyEquiv |X| |Y|, e.toFun = (SSet.toTop.map f).hom

namespace IsRealizationEquivalence

lemma of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] : IsRealizationEquivalence f :=
  ⟨(TopCat.homeoOfIso (SSet.toTop.mapIso (asIso f))).toHomotopyEquiv, rfl⟩

lemma of_isInitial {X Y : SSet.{u}} (f : X ⟶ Y) (hX : IsInitial X) (hY : IsInitial Y) :
    IsRealizationEquivalence f := by
  have : IsIso f := isIso_of_isInitial hX hY f
  exact of_isIso f

lemma of_iso_square {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (eA : A ≅ C) (eB : B ≅ D) (w : f ≫ eB.hom = eA.hom ≫ g)
    (h : IsRealizationEquivalence g) : IsRealizationEquivalence f := by
  obtain ⟨e, he⟩ := h
  exact ⟨TopCat.homotopyEquivOfIsoSquare _ _ (SSet.toTop.mapIso eA)
    (SSet.toTop.mapIso eB) (by simpa using congrArg SSet.toTop.map w) e he, rfl⟩

/-- A finite-simplex product preserves the actual specified equivalence. -/
lemma whiskerRight {X Y : SSet.{u}} {f : X ⟶ Y} (h : IsRealizationEquivalence f)
    (B : SSet.{u}) [LocallyCompactSpace |B|] : IsRealizationEquivalence (f ▷ B) := by
  obtain ⟨e, he⟩ := h
  have := realizationProductComparison_isIso_of_locallyCompact X B
  have := realizationProductComparison_isIso_of_locallyCompact Y B
  refine ⟨TopCat.homotopyEquivOfIsoSquare _ _
    (asIso (prodComparison SSet.toTop X B)) (asIso (prodComparison SSet.toTop Y B))
    (prodComparison_natural_whiskerRight SSet.toTop f)
    (e.prodCongr (ContinuousMap.HomotopyEquiv.refl |B|)) ?_, rfl⟩
  ext x
  change (e.toFun x.1, x.2) = _
  rw [he]
  rfl

/-- Homotopy gluing retains the given fourth map in a map of simplicial
pushouts along monomorphisms. -/
lemma pushout
    {A B C D A' B' C' D' : SSet.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    [Mono i] [Mono i']
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (wi : i ≫ b = a ≫ i') (wf : f ≫ c = a ≫ f')
    (wg : g ≫ d = b ≫ g') (wj : j ≫ d = c ≫ j')
    (ha : IsRealizationEquivalence a) (hb : IsRealizationEquivalence b)
    (hc : IsRealizationEquivalence c) : IsRealizationEquivalence d := by
  obtain ⟨ea, hea⟩ := ha
  obtain ⟨eb, heb⟩ := hb
  obtain ⟨ec, hec⟩ := hc
  refine ⟨TopCat.Pushout.pushoutHomotopyEquivOfMap (sq.map SSet.toTop) (sq'.map SSet.toTop)
    (SSet.homotopyExtensionProperty_realization_mono i)
      (SSet.homotopyExtensionProperty_realization_mono i')
    (SSet.toTop.map a) (SSet.toTop.map b) (SSet.toTop.map c) (SSet.toTop.map d)
    ?_ ?_ ?_ ?_ ea hea eb heb ec hec, rfl⟩
  · simpa only [Functor.map_comp] using congrArg SSet.toTop.map wi
  · simpa only [Functor.map_comp] using congrArg SSet.toTop.map wf
  · simpa only [Functor.map_comp] using congrArg SSet.toTop.map wg
  · simpa only [Functor.map_comp] using congrArg SSet.toTop.map wj

end IsRealizationEquivalence
end SSet
