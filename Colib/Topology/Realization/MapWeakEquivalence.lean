/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.MapEquivalence
public import Colib.Topology.DoubleMappingCylinder.WeakInvariance
public import Colib.Topology.HomotopyPullback.Pushout

/-!
# Complete weak equivalences of original realization maps

The predicate records the literal realized map, including components and
degree zero. Products with locally compact realizations and actual mono
pushouts preserve this property. Pushout gluing uses objectwise weak double
cylinders and their genuine HEP collapse equivalences; no weak-map inverse
or CW Whitehead upgrade is chosen.

Implementation provenance:
`Quillen/Topology/Realization/MapWeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat SSet
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet

/-- A simplicial-set map whose actual topological realization is a weak
homotopy equivalence: it is onto path components and bijective on every
finite-dimensional based homotopy set at every source base point. -/
def IsRealizationWeakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  IsWeakHomotopyEquivalence (SSet.toTop.map f).hom

namespace IsRealizationWeakEquivalence
lemma of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] : IsRealizationWeakEquivalence f :=
  isWeakHomotopyEquivalence_of_homotopyEquiv
    (TopCat.homeoOfIso (SSet.toTop.mapIso (asIso f))).toHomotopyEquiv

lemma of_isInitial {X Y : SSet.{u}} (f : X ⟶ Y) (hX : IsInitial X) (hY : IsInitial Y) :
    IsRealizationWeakEquivalence f := by
  have : IsIso f := isIso_of_isInitial hX hY f
  exact of_isIso f

lemma of_iso_square {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (eA : A ≅ C) (eB : B ≅ D) (w : f ≫ eB.hom = eA.hom ≫ g)
    (h : IsRealizationWeakEquivalence g) : IsRealizationWeakEquivalence f := by
  have hA := isWeakHomotopyEquivalence_of_homotopyEquiv
    (TopCat.homeoOfIso (SSet.toTop.mapIso eA)).toHomotopyEquiv
  have hB := isWeakHomotopyEquivalence_of_homotopyEquiv
    (TopCat.homeoOfIso (SSet.toTop.mapIso eB)).toHomotopyEquiv
  have hw := congrArg (fun k => (SSet.toTop.map k).hom) w
  simp only [Functor.map_comp, TopCat.hom_comp] at hw
  have hh := h.comp hA
  change IsWeakHomotopyEquivalence ((SSet.toTop.map g).hom.comp (SSet.toTop.map eA.hom).hom) at hh
  rw [← hw] at hh
  exact hh.of_comp_right hB

lemma whiskerRight {X Y : SSet.{u}} {f : X ⟶ Y} (h : IsRealizationWeakEquivalence f)
    (B : SSet.{u}) [LocallyCompactSpace |B|] : IsRealizationWeakEquivalence (f ▷ B) := by
  have := realizationProductComparison_isIso_of_locallyCompact X B
  have := realizationProductComparison_isIso_of_locallyCompact Y B
  have hX := isWeakHomotopyEquivalence_of_homotopyEquiv
    (TopCat.homeoOfIso (asIso (CartesianMonoidalCategory.prodComparison SSet.toTop X
      B))).toHomotopyEquiv
  have hY := isWeakHomotopyEquivalence_of_homotopyEquiv
    (TopCat.homeoOfIso (asIso (CartesianMonoidalCategory.prodComparison SSet.toTop Y
      B))).toHomotopyEquiv
  have hw := congrArg TopCat.Hom.hom (prodComparison_natural_whiskerRight SSet.toTop (B := B) f)
  have hp := (h.prodMap_id |B|).comp hX
  change IsWeakHomotopyEquivalence
    (((SSet.toTop.map f).hom.prodMap (ContinuousMap.id |B|)).comp
      (CartesianMonoidalCategory.prodComparison SSet.toTop X B).hom) at hp
  have he : (CartesianMonoidalCategory.prodComparison SSet.toTop Y B).hom.comp (SSet.toTop.map
    (f ▷ B)).hom =
      ((SSet.toTop.map f).hom.prodMap (ContinuousMap.id |B|)).comp
        (CartesianMonoidalCategory.prodComparison SSet.toTop X B).hom := hw
  rw [← he] at hp
  exact hp.of_comp_right hY

lemma pushout
    {A B C D A' B' C' D' : SSet.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    [Mono i] [Mono i']
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (wi : i ≫ b = a ≫ i') (wf : f ≫ c = a ≫ f')
    (wg : g ≫ d = b ≫ g') (wj : j ≫ d = c ≫ j')
    (ha : IsRealizationWeakEquivalence a) (hb : IsRealizationWeakEquivalence b)
    (hc : IsRealizationWeakEquivalence c) : IsRealizationWeakEquivalence d := by
  let a' := SSet.toTop.map a
  let b' := SSet.toTop.map b
  let c' := SSet.toTop.map c
  have wi' : SSet.toTop.map i ≫ b' = a' ≫ SSet.toTop.map i' := by
    simpa only [Functor.map_comp] using congrArg SSet.toTop.map wi
  have wf' : SSet.toTop.map f ≫ c' = a' ≫ SSet.toTop.map f' := by
    simpa only [Functor.map_comp] using congrArg SSet.toTop.map wf
  have wg' : SSet.toTop.map g ≫ SSet.toTop.map d = b' ≫ SSet.toTop.map g' := by
    simpa only [Functor.map_comp] using congrArg SSet.toTop.map wg
  have wj' : SSet.toTop.map j ≫ SSet.toTop.map d = c' ≫ SSet.toTop.map j' := by
    simpa only [Functor.map_comp] using congrArg SSet.toTop.map wj
  have hd := DoubleCylinder.map_isWeakHomotopyEquivalence
    (DoubleCylinder.cylinderSquare (SSet.toTop.map i) (SSet.toTop.map f))
    (DoubleCylinder.cylinderSquare (SSet.toTop.map i') (SSet.toTop.map f'))
    a' b' c' wi' wf' ha hb hc
  have hcollapse := isWeakHomotopyEquivalence_of_homotopyEquiv
    (DoubleCylinder.collapseHomotopyEquiv
      (DoubleCylinder.cylinderSquare (SSet.toTop.map i') (SSet.toTop.map f'))
      (sq'.map SSet.toTop) (SSet.homotopyExtensionProperty_realization_mono i'))
  have hh := hcollapse.comp hd
  change IsWeakHomotopyEquivalence
    ((DoubleCylinder.collapseOfPushout (sq'.map SSet.toTop)).hom.comp
      (CartesianPushout.cylinderMap a' b' c' wi' wf').hom) at hh
  rw [← CartesianPushout.collapse_square (sq.map SSet.toTop) (sq'.map SSet.toTop)
    a' b' c' (SSet.toTop.map d) wi' wf' wg' wj'] at hh
  exact hh.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv
    (DoubleCylinder.collapseHomotopyEquiv
      (DoubleCylinder.cylinderSquare (SSet.toTop.map i) (SSet.toTop.map f))
      (sq.map SSet.toTop) (SSet.homotopyExtensionProperty_realization_mono i)))

end IsRealizationWeakEquivalence
end SSet
