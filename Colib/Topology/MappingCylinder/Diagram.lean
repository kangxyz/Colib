/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Pushout.HomotopyEquivalence
public import Colib.Topology.MappingCylinder.HomotopyExtension
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Pointwise mapping cylinders and their actual colimits. -/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremA/MappingCylinderDiagram.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, prescribed forward
comparisons, deformation homotopies, hypotheses and universes are retained.
Only namespace/import ownership and unnecessary broad imports change.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat
variable {J : Type v} [Category.{w} J] [HasColimitsOfShape J TopCat.{u}]

/-- The terminal cylinder endpoint, natural in a diagram. -/
def diagramCylinderEndpoint (F : J ⥤ TopCat.{u}) : F ⟶ F ⋙ tensorRight TopCat.I where
  app _j := TopCat.ι₁
  naturality _ _ f := (TopCat.ι₁_comp (F.map f)).symm

/-- The mapping cylinder of a natural transformation is an actual pushout
in the functor category, hence an actual pointwise topological mapping cylinder. -/
def mappingCylinderDiagram {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) : J ⥤ TopCat.{u} :=
  pushout (diagramCylinderEndpoint F) η

/-- The natural map from the source cylinder diagram to the pointwise mapping-cylinder diagram of
`η`, given by the first pushout inclusion. -/
def mappingCylinderDiagramLine {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) :
    F ⋙ tensorRight TopCat.I ⟶ mappingCylinderDiagram η := pushout.inl _ _

/-- The natural inclusion of the target diagram `G` into the pointwise mapping-cylinder diagram of
`η`. -/
def mappingCylinderDiagramTarget {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) :
    G ⟶ mappingCylinderDiagram η := pushout.inr _ _

/-- The starting endpoint, natural in the indexing category. -/
def mappingCylinderDiagramStart {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) :
    F ⟶ mappingCylinderDiagram η where
  app j := TopCat.ι₀ ≫ (mappingCylinderDiagramLine η).app j
  naturality i j f := by
    rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc]
    change TopCat.ι₀ ≫ (F ⋙ tensorRight TopCat.I).map f ≫ _ = _
    rw [(mappingCylinderDiagramLine η).naturality f]
    simp only [Category.assoc]

omit [HasColimitsOfShape J TopCat.{u}] in
/-- Evaluating the diagram pushout gives the actual mapping-cylinder square. -/
theorem mappingCylinderDiagramSquare {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) (j : J) :
    IsPushout (TopCat.ι₁ : F.obj j ⟶ F.obj j ⊗ TopCat.I) (η.app j)
      ((mappingCylinderDiagramLine η).app j) ((mappingCylinderDiagramTarget η).app j) :=
  (IsPushout.of_hasPushout (diagramCylinderEndpoint F) η).map ((evaluation J TopCat).obj j)

omit [HasColimitsOfShape J TopCat.{u}] in
/-- Every starting endpoint in the mapping-cylinder diagram has HEP. -/
theorem mappingCylinderDiagramStart_hep {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) (j : J) :
    TopCat.HomotopyExtensionProperty ((mappingCylinderDiagramStart η).app j) :=
  TopCat.homotopyExtensionProperty_mappingCylinderStart (mappingCylinderDiagramSquare η j)

/-- A stagewise homotopy equivalence yields the exact starting-endpoint equivalence. -/
def mappingCylinderDiagramStartHomotopyEquiv {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) (j : J)
    (e : ContinuousMap.HomotopyEquiv (F.obj j) (G.obj j)) (he : e.toFun = (η.app j).hom) :
    ContinuousMap.HomotopyEquiv (F.obj j) ((mappingCylinderDiagram η).obj j) :=
  TopCat.MappingCylinder.mappingCylinderStartHomotopyEquiv (mappingCylinderDiagramSquare η j) e he

omit [HasColimitsOfShape J TopCat.{u}] in
@[simp] theorem mappingCylinderDiagramStartHomotopyEquiv_toFun
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) (j : J)
    (e : ContinuousMap.HomotopyEquiv (F.obj j) (G.obj j)) (he : e.toFun = (η.app j).hom) :
    (mappingCylinderDiagramStartHomotopyEquiv η j e he).toFun =
      ((mappingCylinderDiagramStart η).app j).hom := rfl

/-- Colimits carry the natural endpoint to the actual endpoint after the
canonical cylinder/colimit comparison. -/
theorem colimit_diagramCylinderEndpoint (F : J ⥤ TopCat.{u}) :
    colim.map (diagramCylinderEndpoint F) ≫ (preservesColimitIso (tensorRight TopCat.I) F).inv =
      (TopCat.ι₁ : colimit F ⟶ colimit F ⊗ TopCat.I) := by
  apply colimit.hom_ext
  intro j
  rw [← Category.assoc, colimit.ι_map, Category.assoc, ι_preservesColimitIso_inv]
  exact TopCat.ι₁_comp (colimit.ι F j)

/-- The colimit of pointwise mapping cylinders is itself a mapping cylinder
of the canonical colimit map. -/
theorem mappingCylinderDiagramColimitSquare {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) :
    IsPushout (TopCat.ι₁ : colimit F ⟶ colimit F ⊗ TopCat.I) (colim.map η)
      ((preservesColimitIso (tensorRight TopCat.I) F).hom ≫
        colim.map (mappingCylinderDiagramLine η))
      (colim.map (mappingCylinderDiagramTarget η)) := by
  have sq := (IsPushout.of_hasPushout (diagramCylinderEndpoint F) η).map
    (colim : (J ⥤ TopCat.{u}) ⥤ TopCat.{u})
  apply sq.of_iso (Iso.refl _) (preservesColimitIso (tensorRight TopCat.I) F).symm
    (Iso.refl _) (Iso.refl _)
  · simpa using colimit_diagramCylinderEndpoint F
  · simp
  · simp [mappingCylinderDiagramLine]
  · simp [mappingCylinderDiagramTarget]

/-- The target colimit is an actual strong deformation retract of the colimit
of pointwise mapping cylinders; no inverse-homotopy coherence is assumed. -/
def mappingCylinderDiagramColimitStrongDeformationRetract
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) :
    TopCat.CylinderStrongDeformationRetract (colim.map (mappingCylinderDiagramTarget η)) :=
  TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract
    (mappingCylinderDiagramColimitSquare η)

/-- The actual collapse of the colimit mapping cylinder is a homotopy equivalence. -/
def mappingCylinderDiagramColimitCollapseHomotopyEquiv
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) :
    ContinuousMap.HomotopyEquiv (colimit (mappingCylinderDiagram η) : TopCat.{u}) (colimit G :
      TopCat.{u}) :=
  (mappingCylinderDiagramColimitStrongDeformationRetract η).toHomotopyEquiv.symm

@[simp] theorem mappingCylinderDiagramColimitCollapseHomotopyEquiv_toFun
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) :
    (mappingCylinderDiagramColimitCollapseHomotopyEquiv η).toFun =
      (TopCat.MappingCylinder.mappingCylinderProjection (mappingCylinderDiagramColimitSquare
        η)).hom := rfl

/-- The colimit of starting endpoints is the actual start of the colimit cylinder. -/
theorem colimit_mappingCylinderDiagramStart {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) :
    colim.map (mappingCylinderDiagramStart η) =
      TopCat.ι₀ ≫ (preservesColimitIso (tensorRight TopCat.I) F).hom ≫
        colim.map (mappingCylinderDiagramLine η) := by
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_map, ← Category.assoc (colimit.ι F j) TopCat.ι₀,
    ← TopCat.ι₀_comp, Category.assoc, ← Category.assoc (colimit.ι F j ▷ TopCat.I),
    ]
  have hι : (colimit.ι F j ▷ TopCat.I) ≫ (preservesColimitIso (tensorRight TopCat.I) F).hom =
      colimit.ι (F ⋙ tensorRight TopCat.I) j := ι_preservesColimitIso_hom (tensorRight TopCat.I) F j
  rw [hι, colimit.ι_map]
  rfl

/-- The composite used by sequential invariance is exactly the canonical
colimit map, without an arbitrary homotopy or basepoint substitution. -/
theorem mappingCylinderDiagramColimitCollapse_start {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) :
    colim.map (mappingCylinderDiagramStart η) ≫
      TopCat.MappingCylinder.mappingCylinderProjection (mappingCylinderDiagramColimitSquare η) =
        colim.map η := by
  rw [colimit_mappingCylinderDiagramStart, ← Category.assoc]
  exact TopCat.MappingCylinder.mappingCylinderProjection_start (mappingCylinderDiagramColimitSquare
    η)

/-- The actual relative latching object for a mapping-cylinder diagram. -/
def mappingCylinderLatching {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) {j k : J} (a : j ⟶ k) : TopCat.{u} :=
  pushout (F.map a) ((mappingCylinderDiagramStart η).app j)

/-- The canonical map from the relative latching pushout to the next cylinder. -/
def mappingCylinderLatchingMap {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) {j k : J} (a : j ⟶ k) :
    mappingCylinderLatching η a ⟶ (mappingCylinderDiagram η).obj k :=
  pushout.desc ((mappingCylinderDiagramStart η).app k) ((mappingCylinderDiagram η).map a)
    ((mappingCylinderDiagramStart η).naturality a)

omit [HasColimitsOfShape J TopCat.{u}] in
@[reassoc (attr := simp)] theorem mappingCylinderLatchingMap_inl
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) {j k : J} (a : j ⟶ k) :
    pushout.inl (F.map a) ((mappingCylinderDiagramStart η).app j) ≫ mappingCylinderLatchingMap η a =
      (mappingCylinderDiagramStart η).app k := pushout.inl_desc _ _ _

omit [HasColimitsOfShape J TopCat.{u}] in
@[reassoc (attr := simp)] theorem mappingCylinderLatchingMap_inr
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) {j k : J} (a : j ⟶ k) :
    pushout.inr (F.map a) ((mappingCylinderDiagramStart η).app j) ≫ mappingCylinderLatchingMap η a =
      (mappingCylinderDiagram η).map a := pushout.inr_desc _ _ _

/-- A homotopy-equivalent coefficient map and a cofibrant source transition
make the actual cylinder latching map a homotopy equivalence. -/
def mappingCylinderLatchingHomotopyEquiv {F G : J ⥤ TopCat.{u}} (η : F ⟶ G)
    {j k : J} (a : j ⟶ k) (ha : TopCat.HomotopyExtensionProperty (F.map a))
    (e : ∀ j, ContinuousMap.HomotopyEquiv (F.obj j) (G.obj j))
    (he : ∀ j, (e j).toFun = (η.app j).hom) :
    ContinuousMap.HomotopyEquiv (mappingCylinderLatching η a) ((mappingCylinderDiagram η).obj k) :=
      by
  let ej := mappingCylinderDiagramStartHomotopyEquiv η j (e j) (he j)
  let ek := mappingCylinderDiagramStartHomotopyEquiv η k (e k) (he k)
  let eq := TopCat.Pushout.pushoutHomotopyEquivAlongCofibration
    (IsPushout.of_hasPushout (F.map a) ((mappingCylinderDiagramStart η).app j)) ha ej rfl
  exact TopCat.homotopyEquivCancelLeft (b := mappingCylinderLatchingMap η a) eq rfl ek (by
    rw [mappingCylinderLatchingMap_inl]
    rfl)

omit [HasColimitsOfShape J TopCat.{u}] in
@[simp] theorem mappingCylinderLatchingHomotopyEquiv_toFun
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) {j k : J} (a : j ⟶ k)
    (ha : TopCat.HomotopyExtensionProperty (F.map a))
    (e : ∀ j, ContinuousMap.HomotopyEquiv (F.obj j) (G.obj j))
    (he : ∀ j, (e j).toFun = (η.app j).hom) :
    (mappingCylinderLatchingHomotopyEquiv η a ha e he).toFun = (mappingCylinderLatchingMap η a).hom
      := rfl

end TopCat
