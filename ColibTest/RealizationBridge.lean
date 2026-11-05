/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.HomotopyBridge

/-! The comparison is the actual cylinder map, with its two ordered endpoints,
inverse naturality, concrete interval lift and fixed-vertex hypothesis. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial Topology unitInterval

universe u v

example (X : SSet.{u}) : IsIso (realizationCylinderComparison X) := inferInstance

example (X : SSet.{u}) :
    (realizationCylinderIso X).hom = realizationCylinderComparison X := rfl

example (X : SSet.{u}) :
    SSet.toTop.map (SSet.ι₀ (X := X)) ≫ realizationCylinderComparison X = TopCat.ι₀ :=
  realizationCylinderComparison_zero X

example (X : SSet.{u}) :
    SSet.toTop.map (SSet.ι₁ (X := X)) ≫ realizationCylinderComparison X = TopCat.ι₁ :=
  realizationCylinderComparison_one X

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    (realizationCylinderIso X).inv ≫ SSet.toTop.map (f ▷ Δ[1]) =
      (SSet.toTop.map f ▷ TopCat.I) ≫ (realizationCylinderIso Y).inv :=
  realizationCylinderIso_inv_naturality f

example {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (t : unitInterval) (x : |X|) :
    realizationSimplicialHomotopy H (t, x) =
      SSet.toTop.map H.h ((realizationCylinderIso X).inv (x, ULift.up t)) := rfl

example {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : SSet.yonedaEquiv.symm x ▷ Δ[1] ≫ H.h =
      fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm y) (t : unitInterval) :
    realizationSimplicialHomotopy H (t, realizationPoint x) = realizationPoint y :=
  realizationSimplicialHomotopy_fixed_vertex H x y h t

example {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C)
    (h : F.obj c = G.obj c) (hα : α.app c = eqToHom h) :
    (classifyingSpaceMap F).hom.HomotopyRel (classifyingSpaceMap G).hom
      {classifyingSpacePoint c} :=
  classifyingSpaceNaturalTransformationBasedHomotopy α c h hα

example (X : SSet.{u}) :
    realizationCylinderComparison X ≫ (realizationCylinderIso X).inv = 𝟙 _ :=
  (realizationCylinderIso X).hom_inv_id

example (X : SSet.{u}) :
    (realizationCylinderIso X).inv ≫ realizationCylinderComparison X = 𝟙 _ :=
  (realizationCylinderIso X).inv_hom_id

example (X : SSet.{u}) :
    realizationCylinderComparisonNatTrans.app X = realizationCylinderComparison X := rfl

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map (f ▷ Δ[1]) ≫ (realizationCylinderIso Y).hom =
      (realizationCylinderIso X).hom ≫ (SSet.toTop.map f ▷ TopCat.I) :=
  realizationCylinderComparison_naturality f

example (X : SSet.{u}) :
    TopCat.ι₀ ≫ (realizationCylinderIso X).inv = SSet.toTop.map SSet.ι₀ :=
  realizationCylinderIso_inv_zero X

example (X : SSet.{u}) :
    TopCat.ι₁ ≫ (realizationCylinderIso X).inv = SSet.toTop.map SSet.ι₁ :=
  realizationCylinderIso_inv_one X

example {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) (x : |X|) :
    realizationSimplicialHomotopy H (0, x) = SSet.toTop.map f x :=
  (realizationSimplicialHomotopy H).map_zero_left x

example {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) (x : |X|) :
    realizationSimplicialHomotopy H (1, x) = SSet.toTop.map g x :=
  (realizationSimplicialHomotopy H).map_one_left x

example {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    Continuous (realizationSimplicialHomotopy H) :=
  (realizationSimplicialHomotopy H).continuous

example {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy α (t, x) =
      realizationSimplicialHomotopy (naturalTransformationNerveHomotopy α) (t, x) := rfl

example {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C)
    (h : F.obj c = G.obj c) (hα : α.app c = eqToHom h) :
    (classifyingSpaceNaturalTransformationBasedHomotopy α c h hα).toHomotopy =
      classifyingSpaceNaturalTransformationHomotopy α := rfl
