/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References

public import Colib.Topology.MappingCylinder.PushoutCollapse
public import Colib.Topology.MappingCylinder.HomotopyExtension
public import Colib.Topology.Pushout.Homotopy

/-!
# Homotopy-equivalence gluing and cancellation for pushouts
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Pushout/HomotopyEquivalence.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, homotopies and
pushout universal properties are retained, with native namespace and import ownership.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat

/-- Cobase change of any actual homotopy equivalence along a map with HEP
is an actual homotopy equivalence. Its forward map is the canonical map
from the other corner into the pushout. -/
def Pushout.pushoutHomotopyEquivAlongCofibration {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : TopCat.HomotopyExtensionProperty i)
    (e : ContinuousMap.HomotopyEquiv A C) (he : e.toFun = f.hom) :
    ContinuousMap.HomotopyEquiv B D := by
  let M := pushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f
  let l : A ⊗ TopCat.I ⟶ M := pushout.inl _ _
  let c : C ⟶ M := pushout.inr _ _
  let sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c := IsPushout.of_hasPushout _ _
  let Q := pushout i (TopCat.ι₀ ≫ l)
  let b : B ⟶ Q := pushout.inl _ _
  let m : M ⟶ Q := pushout.inr _ _
  let sqQ : IsPushout i (TopCat.ι₀ ≫ l) b m := IsPushout.of_hasPushout _ _
  let e₀ := TopCat.MappingCylinder.mappingCylinderStartHomotopyEquiv sqM e he
  let e₁ := TopCat.pushoutHomotopyEquivOfCofibration sqQ.flip
    (TopCat.homotopyExtensionProperty_mappingCylinderStart sqM) e₀ rfl
  let e₂ := TopCat.MappingCylinder.mappingCylinderPushoutCollapseHomotopyEquiv sqM sqQ sq hi
  let E := e₁.trans e₂
  have hE : E.toFun = g.hom := by
    change (b ≫ sqQ.desc g (TopCat.MappingCylinder.mappingCylinderProjection sqM ≫ j) _).hom =
      g.hom
    rw [sqQ.inl_desc]
  exact { E with
    toFun := g.hom
    left_inv := by simpa only [hE] using E.left_inv
    right_inv := by simpa only [hE] using E.right_inv }

@[simp]
theorem Pushout.pushoutHomotopyEquivAlongCofibration_toFun {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : TopCat.HomotopyExtensionProperty i)
    (e : ContinuousMap.HomotopyEquiv A C) (he : e.toFun = f.hom) :
    (TopCat.Pushout.pushoutHomotopyEquivAlongCofibration sq hi e he).toFun = g.hom := rfl

/-- Cancellation of a specified homotopy equivalence from the left of a
composite, retaining exactly the specified second map. -/
def homotopyEquivCancelLeft {A B C : TopCat.{u}} {a : A ⟶ B} {b : B ⟶ C}
    (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = a.hom)
    (e' : ContinuousMap.HomotopyEquiv A C) (he' : e'.toFun = (a ≫ b).hom) :
    ContinuousMap.HomotopyEquiv B C := by
  let H := (ContinuousMap.Homotopy.refl b.hom).comp e.right_inv.some.symm
  apply TopCat.homotopyEquivOfHomotopy (f := b) (e.symm.trans e')
  exact H.cast (by ext; rfl) (by
    change b.hom.comp (e.toFun.comp e.invFun) = e'.toFun.comp e.invFun
    rw [he, he']
    rfl)

@[simp]
theorem homotopyEquivCancelLeft_toFun {A B C : TopCat.{u}} {a : A ⟶ B} {b : B ⟶ C}
    (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = a.hom)
    (e' : ContinuousMap.HomotopyEquiv A C) (he' : e'.toFun = (a ≫ b).hom) :
    (TopCat.homotopyEquivCancelLeft e he e' he').toFun = b.hom := rfl

/-- The homotopy gluing theorem for a map between two actual topological
pushout squares. Three homotopy-equivalence components and HEP for the
corresponding attaching legs imply that the canonical fourth component is
an actual homotopy equivalence. -/
def Pushout.pushoutHomotopyEquiv
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : TopCat.HomotopyExtensionProperty i) (hi' : TopCat.HomotopyExtensionProperty i')
    (ea : ContinuousMap.HomotopyEquiv A A')
    (eb : ContinuousMap.HomotopyEquiv B B')
    (ec : ContinuousMap.HomotopyEquiv C C')
    (wi : i ≫ TopCat.ofHom eb.toFun = TopCat.ofHom ea.toFun ≫ i')
    (wf : f ≫ TopCat.ofHom ec.toFun = TopCat.ofHom ea.toFun ≫ f') :
    ContinuousMap.HomotopyEquiv D D' := by
  let a : A ⟶ A' := TopCat.ofHom ea.toFun
  let b : B ⟶ B' := TopCat.ofHom eb.toFun
  let c : C ⟶ C' := TopCat.ofHom ec.toFun
  let E := pushout i a
  let be : B ⟶ E := pushout.inl _ _
  let ae : A' ⟶ E := pushout.inr _ _
  let sqE : IsPushout i a be ae := IsPushout.of_hasPushout _ _
  let x : E ⟶ B' := sqE.desc b i' wi
  have hbx : be ≫ x = b := sqE.inl_desc _ _ _
  have hax : ae ≫ x = i' := sqE.inr_desc _ _ _
  let ebe := TopCat.Pushout.pushoutHomotopyEquivAlongCofibration sqE hi ea rfl
  let ex := TopCat.homotopyEquivCancelLeft (a := be) (b := x) ebe
    (TopCat.Pushout.pushoutHomotopyEquivAlongCofibration_toFun sqE hi ea rfl) eb (by
    rw [hbx]
    rfl)
  let P := pushout i (f ≫ c)
  let bp : B ⟶ P := pushout.inl _ _
  let cp : C' ⟶ P := pushout.inr _ _
  let sqP : IsPushout i (f ≫ c) bp cp := IsPushout.of_hasPushout _ _
  have sqPa : IsPushout i (a ≫ f') bp cp := by
    have wf' : f ≫ c = a ≫ f' := wf
    rw [← wf']
    exact sqP
  let ep : E ⟶ P := sqE.desc bp (f' ≫ cp) (by rw [← Category.assoc, ← wf, sqP.w])
  have hbep : be ≫ ep = bp := sqE.inl_desc _ _ _
  have haep : ae ≫ ep = f' ≫ cp := sqE.inr_desc _ _ _
  have sqEP : IsPushout ae f' ep cp := by
    apply IsPushout.of_top _ haep sqE
    simpa only [hbep] using sqPa
  let d : D ⟶ P := sq.desc bp (c ≫ cp) (by rw [← Category.assoc, sqP.w])
  have hgd : g ≫ d = bp := sq.inl_desc _ _ _
  have hjd : j ≫ d = c ≫ cp := sq.inr_desc _ _ _
  have sqDP : IsPushout j c d cp := by
    apply IsPushout.of_top _ hjd sq
    simpa only [hgd] using sqP
  let ed := TopCat.Pushout.pushoutHomotopyEquivAlongCofibration sqDP
    (TopCat.homotopyExtensionProperty_pushout sq hi) ec rfl
  let ey := TopCat.Pushout.pushoutHomotopyEquivOverBase sqEP sq'
    (TopCat.homotopyExtensionProperty_pushout sqE hi) hi' ex hax
  let y : P ⟶ D' := TopCat.ofHom ey.toFun
  have hepy : ep ≫ y = x ≫ g' := sqEP.inl_desc _ _ _
  have hcpy : cp ≫ y = j' := sqEP.inr_desc _ _ _
  have hw : i ≫ b ≫ g' = f ≫ c ≫ j' := by
    rw [← Category.assoc i b, wi, Category.assoc, sq'.w,
      ← Category.assoc a f', ← wf, Category.assoc]
  let q : D ⟶ D' := sq.desc (b ≫ g') (c ≫ j') hw
  have hdq : d ≫ y = q := by
    apply sq.hom_ext
    · rw [← Category.assoc, hgd, ← hbep, Category.assoc, hepy,
        ← Category.assoc, hbx]
      exact (sq.inl_desc _ _ _).symm
    · rw [← Category.assoc, hjd, Category.assoc, hcpy]
      exact (sq.inr_desc _ _ _).symm
  let et := ed.trans ey
  have het : et.toFun = q.hom := congrArg TopCat.Hom.hom hdq
  exact { et with
    toFun := q.hom
    left_inv := by simpa only [het] using et.left_inv
    right_inv := by simpa only [het] using et.right_inv }

@[reassoc (attr := simp)]
theorem Pushout.pushoutHomotopyEquiv_inl
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : TopCat.HomotopyExtensionProperty i) (hi' : TopCat.HomotopyExtensionProperty i')
    (ea : ContinuousMap.HomotopyEquiv A A')
    (eb : ContinuousMap.HomotopyEquiv B B')
    (ec : ContinuousMap.HomotopyEquiv C C')
    (wi : i ≫ TopCat.ofHom eb.toFun = TopCat.ofHom ea.toFun ≫ i')
    (wf : f ≫ TopCat.ofHom ec.toFun = TopCat.ofHom ea.toFun ≫ f') :
    g ≫ TopCat.ofHom (TopCat.Pushout.pushoutHomotopyEquiv sq sq' hi hi' ea eb ec wi wf).toFun =
      TopCat.ofHom eb.toFun ≫ g' := by
  simp only [TopCat.Pushout.pushoutHomotopyEquiv, TopCat.ofHom_hom]
  exact sq.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem Pushout.pushoutHomotopyEquiv_inr
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : TopCat.HomotopyExtensionProperty i) (hi' : TopCat.HomotopyExtensionProperty i')
    (ea : ContinuousMap.HomotopyEquiv A A')
    (eb : ContinuousMap.HomotopyEquiv B B')
    (ec : ContinuousMap.HomotopyEquiv C C')
    (wi : i ≫ TopCat.ofHom eb.toFun = TopCat.ofHom ea.toFun ≫ i')
    (wf : f ≫ TopCat.ofHom ec.toFun = TopCat.ofHom ea.toFun ≫ f') :
    j ≫ TopCat.ofHom (TopCat.Pushout.pushoutHomotopyEquiv sq sq' hi hi' ea eb ec wi wf).toFun =
      TopCat.ofHom ec.toFun ≫ j' := by
  simp only [TopCat.Pushout.pushoutHomotopyEquiv, TopCat.ofHom_hom]
  exact sq.inr_desc _ _ _

/-- A formulation of homotopy gluing for four specified vertical maps.
The equivalences are required to represent the actual three component
maps, and the constructed equivalence represents the actual fourth map. -/
def Pushout.pushoutHomotopyEquivOfMap
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : TopCat.HomotopyExtensionProperty i) (hi' : TopCat.HomotopyExtensionProperty i')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (wi : i ≫ b = a ≫ i') (wf : f ≫ c = a ≫ f')
    (wg : g ≫ d = b ≫ g') (wj : j ≫ d = c ≫ j')
    (ea : ContinuousMap.HomotopyEquiv A A') (ha : ea.toFun = a.hom)
    (eb : ContinuousMap.HomotopyEquiv B B') (hb : eb.toFun = b.hom)
    (ec : ContinuousMap.HomotopyEquiv C C') (hc : ec.toFun = c.hom) :
    ContinuousMap.HomotopyEquiv D D' := by
  have hai : TopCat.ofHom ea.toFun = a := by rw [ha]; rfl
  have hbi : TopCat.ofHom eb.toFun = b := by rw [hb]; rfl
  have hci : TopCat.ofHom ec.toFun = c := by rw [hc]; rfl
  let E := TopCat.Pushout.pushoutHomotopyEquiv sq sq' hi hi' ea eb ec
    (by simpa only [hai, hbi] using wi) (by simpa only [hai, hci] using wf)
  have hE : TopCat.ofHom E.toFun = d := by
    apply sq.hom_ext
    · rw [TopCat.Pushout.pushoutHomotopyEquiv_inl, hbi, wg]
    · rw [TopCat.Pushout.pushoutHomotopyEquiv_inr, hci, wj]
  have hE' : E.toFun = d.hom := congrArg TopCat.Hom.hom hE
  exact { E with
    toFun := d.hom
    left_inv := by simpa only [hE'] using E.left_inv
    right_inv := by simpa only [hE'] using E.right_inv }

@[simp]
theorem Pushout.pushoutHomotopyEquivOfMap_toFun
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : TopCat.HomotopyExtensionProperty i) (hi' : TopCat.HomotopyExtensionProperty i')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (wi : i ≫ b = a ≫ i') (wf : f ≫ c = a ≫ f')
    (wg : g ≫ d = b ≫ g') (wj : j ≫ d = c ≫ j')
    (ea : ContinuousMap.HomotopyEquiv A A') (ha : ea.toFun = a.hom)
    (eb : ContinuousMap.HomotopyEquiv B B') (hb : eb.toFun = b.hom)
    (ec : ContinuousMap.HomotopyEquiv C C') (hc : ec.toFun = c.hom) :
    (TopCat.Pushout.pushoutHomotopyEquivOfMap sq sq' hi hi' a b c d wi wf wg wj ea ha eb hb ec
      hc).toFun =
      d.hom := rfl


end TopCat

attribute [colib_tag "COL-0214",
  colib_ref "HatcherAT" "Chapter 0, Exercise 27, page 20"
    "adaptation"
    "Cobase-change equivalence extended to a map of actual HEP pushout squares"]
  TopCat.Pushout.pushoutHomotopyEquivAlongCofibration
  TopCat.Pushout.pushoutHomotopyEquivOfMap
  TopCat.Pushout.pushoutHomotopyEquivOfMap_toFun
