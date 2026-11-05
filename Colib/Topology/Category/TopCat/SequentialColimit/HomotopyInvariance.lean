/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References

public import Colib.Topology.Category.TopCat.SequentialColimit.CobaseChange
public import Colib.Topology.MappingCylinder.Latching

/-!
# Homotopy invariance of sequential colimits of cofibrations

A natural transformation which is a homotopy equivalence at every stage
induces an actual homotopy equivalence of sequential colimits whenever
both sequences have the homotopy extension property at each successor.
The inverse and its coherent homotopies are constructed using mapping
cylinders, relative latching pushouts, and timed sequential deformations.
-/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremA/SequentialHomotopyInvariance.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, prescribed forward
comparisons, deformation homotopies, hypotheses and universes are retained.
Only namespace/import ownership and unnecessary broad imports change.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits
open scoped Topology unitInterval

universe u v w
set_option backward.isDefEq.respectTransparency false

namespace TopCat

/-- Stagewise actual homotopy equivalences between sequential diagrams of
cofibrations induce a genuine homotopy equivalence of their actual
colimits. No compatibility of the given inverse maps or homotopies is
assumed. The specified natural transformation is retained exactly. -/
def sequentialColimitHomotopyEquiv {F G : ℕ ⥤ TopCat.{u}}
    (η : F ⟶ G)
    (hF : ∀ n, TopCat.HomotopyExtensionProperty (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, TopCat.HomotopyExtensionProperty (G.map (homOfLE (Nat.le_succ n))))
    (e : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (G.obj n))
    (he : ∀ n, (e n).toFun = (η.app n).hom) :
    ContinuousMap.HomotopyEquiv (colimit F : TopCat.{u}) (colimit G : TopCat.{u}) := by
  let S := mappingCylinderDiagramStart η
  let E₀ := sequentialColimitHomotopyEquivOfLatching S
    (colimit.cocone F) (colimit.isColimit F)
    (colimit.cocone (mappingCylinderDiagram η)) (colimit.isColimit (mappingCylinderDiagram η))
    (mappingCylinderDiagramStart_hep η 0)
    (mappingCylinderDiagramStartHomotopyEquiv η 0 (e 0) (he 0)) rfl
    (fun n ↦ mappingCylinderLatchingMap_hep η (homOfLE (Nat.le_succ n)) (hF n) (hG n))
    (fun n ↦ mappingCylinderLatchingHomotopyEquiv η (homOfLE (Nat.le_succ n)) (hF n) e he)
    (fun _ ↦ rfl)
  let E : ContinuousMap.HomotopyEquiv (colimit F : TopCat.{u}) (colimit G : TopCat.{u}) :=
    E₀.trans (mappingCylinderDiagramColimitCollapseHomotopyEquiv η)
  have hE : E.toFun = (colim.map η).hom := by
    change (colim.map (mappingCylinderDiagramStart η) ≫
      TopCat.MappingCylinder.mappingCylinderProjection (mappingCylinderDiagramColimitSquare η)).hom
        = _
    rw [mappingCylinderDiagramColimitCollapse_start]
  exact { E with
    toFun := (colim.map η).hom
    left_inv := by simpa only [hE] using E.left_inv
    right_inv := by simpa only [hE] using E.right_inv }

@[simp]
theorem sequentialColimitHomotopyEquiv_toFun {F G : ℕ ⥤ TopCat.{u}}
    (η : F ⟶ G)
    (hF : ∀ n, TopCat.HomotopyExtensionProperty (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, TopCat.HomotopyExtensionProperty (G.map (homOfLE (Nat.le_succ n))))
    (e : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (G.obj n))
    (he : ∀ n, (e n).toFun = (η.app n).hom) :
    (sequentialColimitHomotopyEquiv η hF hG e he).toFun = (colim.map η).hom := rfl

/-- Transport an actual equivalence of canonical colimits to any specified
colimit cocones, retaining their canonical comparison map. -/
def colimitHomotopyEquivOfCocones
    {J : Type v} [Category.{w} J] [HasColimitsOfShape J TopCat.{u}]
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G)
    (E : ContinuousMap.HomotopyEquiv (colimit F : TopCat.{u}) (colimit G : TopCat.{u}))
    (hE : E.toFun = (colim.map η).hom)
    (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d) :
    ContinuousMap.HomotopyEquiv c.pt d.pt := by
  let i := hc.coconePointUniqueUpToIso (colimit.isColimit F)
  let j := (colimit.isColimit G).coconePointUniqueUpToIso hd
  let E' : ContinuousMap.HomotopyEquiv c.pt d.pt :=
    ((TopCat.homeoOfIso i).toHomotopyEquiv.trans E).trans
      (TopCat.homeoOfIso j).toHomotopyEquiv
  have heq : i.hom ≫ colim.map η ≫ j.hom = hc.map d η := by
    apply hc.hom_ext
    intro n
    rw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    change colimit.ι F n ≫ colim.map η ≫ j.hom = _
    rw [colimit.ι_map_assoc]
    change η.app n ≫ (colimit.cocone G).ι.app n ≫ j.hom = _
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom, hc.ι_map]
  have hE' : E'.toFun = (hc.map d η).hom := by
    change j.hom.hom.comp (E.toFun.comp i.hom.hom) = _
    rw [hE]
    exact congrArg TopCat.Hom.hom heq
  exact { E' with
    toFun := (hc.map d η).hom
    left_inv := by simpa only [hE'] using E'.left_inv
    right_inv := by simpa only [hE'] using E'.right_inv }

@[simp]
theorem colimitHomotopyEquivOfCocones_toFun
    {J : Type v} [Category.{w} J] [HasColimitsOfShape J TopCat.{u}]
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G)
    (E : ContinuousMap.HomotopyEquiv (colimit F : TopCat.{u}) (colimit G : TopCat.{u}))
    (hE : E.toFun = (colim.map η).hom)
    (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d) :
    (colimitHomotopyEquivOfCocones η E hE c hc d hd).toFun = (hc.map d η).hom := rfl

/-- The cocone form of sequential homotopy invariance, suitable for actual
skeletal exhaustions and other explicitly presented colimits. -/
def sequentialCoconeHomotopyEquiv {F G : ℕ ⥤ TopCat.{u}}
    (η : F ⟶ G)
    (hF : ∀ n, TopCat.HomotopyExtensionProperty (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, TopCat.HomotopyExtensionProperty (G.map (homOfLE (Nat.le_succ n))))
    (e : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (G.obj n))
    (he : ∀ n, (e n).toFun = (η.app n).hom)
    (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d) :
    ContinuousMap.HomotopyEquiv c.pt d.pt :=
  colimitHomotopyEquivOfCocones η (sequentialColimitHomotopyEquiv η hF hG e he) rfl c hc d hd

@[simp]
theorem sequentialCoconeHomotopyEquiv_toFun {F G : ℕ ⥤ TopCat.{u}}
    (η : F ⟶ G)
    (hF : ∀ n, TopCat.HomotopyExtensionProperty (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, TopCat.HomotopyExtensionProperty (G.map (homOfLE (Nat.le_succ n))))
    (e : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (G.obj n))
    (he : ∀ n, (e n).toFun = (η.app n).hom)
    (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d) :
    (sequentialCoconeHomotopyEquiv η hF hG e he c hc d hd).toFun = (hc.map d η).hom := rfl

end TopCat

attribute [colib_tag "COL-0215",
  colib_ref "HatcherAT" "Chapter 0, proof of Proposition 0.16, page 15"
    "background"
    "Shrinking stationary intervals; the general sequential HEP comparison is proved here"]
  TopCat.sequentialColimitHomotopyEquiv
  TopCat.sequentialCoconeHomotopyEquiv
  TopCat.sequentialCoconeHomotopyEquiv_toFun
