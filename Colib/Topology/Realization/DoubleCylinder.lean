/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.CylinderIso
public import Colib.Topology.Realization.CylinderEndpoints
public import Colib.Topology.DoubleMappingCylinder.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The actual simplicial double cylinder realizes to the topological double cylinder

The comparison is a categorical isomorphism, hence an actual homeomorphism.
Its cylinder and endpoint formulas retain the original attaching maps.


Implementation provenance:
`Quillen/Topology/Realization/DoubleCylinder.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat SSet
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat

/-- The realization of the categorical binary coproduct is the literal topological sum. -/
def realizationBinarySumIso (X Y : SSet.{u}) :
    |X ⨿ Y| ≅ TopCat.of (|X| ⊕ |Y|) :=
  (isColimitOfHasBinaryCoproductOfPreservesColimit SSet.toTop X Y).coconePointUniqueUpToIso
    (TopCat.binaryCofanIsColimit |X| |Y|)

@[reassoc (attr := simp)]
theorem realizationBinarySumIso_inl (X Y : SSet.{u}) :
    SSet.toTop.map (coprod.inl : X ⟶ X ⨿ Y) ≫ (realizationBinarySumIso X Y).hom =
      (TopCat.binaryCofan |X| |Y|).inl :=
  (isColimitOfHasBinaryCoproductOfPreservesColimit SSet.toTop X
    Y).comp_coconePointUniqueUpToIso_hom (TopCat.binaryCofanIsColimit |X| |Y|)
      ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem realizationBinarySumIso_inr (X Y : SSet.{u}) :
    SSet.toTop.map (coprod.inr : Y ⟶ X ⨿ Y) ≫ (realizationBinarySumIso X Y).hom =
      (TopCat.binaryCofan |X| |Y|).inr :=
  (isColimitOfHasBinaryCoproductOfPreservesColimit SSet.toTop X
    Y).comp_coconePointUniqueUpToIso_hom (TopCat.binaryCofanIsColimit |X| |Y|)
      ⟨WalkingPair.right⟩

namespace DoubleCylinder

/-- Both simplicial cylinder endpoints together. -/
def simplicialEndpoints (X : SSet.{u}) : X ⨿ X ⟶ X ⊗ Δ[1] :=
  coprod.desc SSet.ι₀ SSet.ι₁

variable {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)

/-- The actual simplicial pushout defining the double cylinder. -/
def simplicial : SSet.{u} := pushout (simplicialEndpoints X) (coprod.map f g)

/-- The original cylinder leg of the simplicial pushout. -/
def simplicialCylinder : X ⊗ Δ[1] ⟶ simplicial f g :=
  pushout.inl (simplicialEndpoints X) (coprod.map f g)

/-- The original endpoint leg of the simplicial pushout. -/
def simplicialEnds : Y ⨿ Z ⟶ simplicial f g :=
  pushout.inr (simplicialEndpoints X) (coprod.map f g)

/-- The original simplicial pushout square. -/
theorem simplicial_isPushout :
    IsPushout (simplicialEndpoints X) (coprod.map f g)
      (simplicialCylinder f g) (simplicialEnds f g) :=
  IsPushout.of_hasPushout _ _

/-- The entire endpoint pair realizes to the literal topological endpoint pair. -/
theorem realizationEndpoints_square :
    SSet.toTop.map (simplicialEndpoints X) ≫ (realizationCylinderIso X).hom =
      (realizationBinarySumIso X X).hom ≫ TopCat.intervalEndpoints |X| := by
  apply (isColimitOfHasBinaryCoproductOfPreservesColimit SSet.toTop X X).hom_ext
  intro j
  cases j with
  | mk j =>
    cases j
    · change SSet.toTop.map (coprod.inl : X ⟶ X ⨿ X) ≫ _ =
        SSet.toTop.map (coprod.inl : X ⟶ X ⨿ X) ≫ _
      rw [← Category.assoc, ← Functor.map_comp]
      simp only [simplicialEndpoints, coprod.inl_desc]
      rw [realizationBinarySumIso_inl_assoc]
      exact realizationCylinderComparison_zero X
    · change SSet.toTop.map (coprod.inr : X ⟶ X ⨿ X) ≫ _ =
        SSet.toTop.map (coprod.inr : X ⟶ X ⨿ X) ≫ _
      rw [← Category.assoc, ← Functor.map_comp]
      simp only [simplicialEndpoints, coprod.inr_desc]
      rw [realizationBinarySumIso_inr_assoc]
      exact realizationCylinderComparison_one X

/-- The attaching map realizes to the original topological attaching map. -/
theorem realizationEndMap_square :
    SSet.toTop.map (coprod.map f g) ≫ (realizationBinarySumIso Y Z).hom =
      (realizationBinarySumIso X X).hom ≫
        endMap (SSet.toTop.map f) (SSet.toTop.map g) := by
  apply (isColimitOfHasBinaryCoproductOfPreservesColimit SSet.toTop X X).hom_ext
  intro j
  cases j with
  | mk j =>
    cases j
    · change SSet.toTop.map (coprod.inl : X ⟶ X ⨿ X) ≫ _ =
        SSet.toTop.map (coprod.inl : X ⟶ X ⨿ X) ≫ _
      rw [← Category.assoc, ← Functor.map_comp, coprod.inl_map, Functor.map_comp]
      simp only [Category.assoc, realizationBinarySumIso_inl,
        realizationBinarySumIso_inl_assoc]
      rfl
    · change SSet.toTop.map (coprod.inr : X ⟶ X ⨿ X) ≫ _ =
        SSet.toTop.map (coprod.inr : X ⟶ X ⨿ X) ≫ _
      rw [← Category.assoc, ← Functor.map_comp, coprod.inr_map, Functor.map_comp]
      simp only [Category.assoc, realizationBinarySumIso_inr,
        realizationBinarySumIso_inr_assoc]
      rfl

/-- Cylinder leg in genuine topological coordinates. -/
def realizedCylinder : |X| ⊗ TopCat.I ⟶ |simplicial f g| :=
  (realizationCylinderIso X).inv ≫ SSet.toTop.map (simplicialCylinder f g)

/-- Endpoint leg in the literal topological sum. -/
def realizedEnds : TopCat.of (|Y| ⊕ |Z|) ⟶ |simplicial f g| :=
  (realizationBinarySumIso Y Z).inv ≫ SSet.toTop.map (simplicialEnds f g)

/-- The realized simplicial double cylinder is an actual displayed topological pushout. -/
theorem realized_isPushout :
    IsPushout (TopCat.intervalEndpoints |X|)
      (endMap (SSet.toTop.map f) (SSet.toTop.map g))
      (realizedCylinder f g) (realizedEnds f g) := by
  apply ((simplicial_isPushout f g).map SSet.toTop).of_iso
    (realizationBinarySumIso X X) (realizationCylinderIso X)
    (realizationBinarySumIso Y Z) (Iso.refl _)
  · exact realizationEndpoints_square
  · exact realizationEndMap_square f g
  · simp [realizedCylinder]
  · simp [realizedEnds]

variable {D : TopCat.{u}} {l : |X| ⊗ TopCat.I ⟶ D}
  {e : TopCat.of (|Y| ⊕ |Z|) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints |X|)
    (endMap (SSet.toTop.map f) (SSet.toTop.map g)) l e)

/-- The canonical isomorphism to any displayed topological double cylinder. -/
def realizationIso : |simplicial f g| ≅ D :=
  (realized_isPushout f g).isoIsPushout _ _ sq

/-- The corresponding actual homeomorphism, with no weak-equivalence upgrade. -/
def realizationHomeomorph : |simplicial f g| ≃ₜ D :=
  TopCat.homeoOfIso (realizationIso f g sq)

@[reassoc (attr := simp)]
theorem realizedCylinder_realizationIso :
    realizedCylinder f g ≫ (realizationIso f g sq).hom = l :=
  IsPushout.inl_isoIsPushout_hom _ _ (realized_isPushout f g) sq

@[reassoc (attr := simp)]
theorem realizedEnds_realizationIso :
    realizedEnds f g ≫ (realizationIso f g sq).hom = e :=
  IsPushout.inr_isoIsPushout_hom _ _ (realized_isPushout f g) sq

/-- Exact formula on the original realized simplicial cylinder leg. -/
@[reassoc (attr := simp)]
theorem realizationIso_cylinder :
    SSet.toTop.map (simplicialCylinder f g) ≫ (realizationIso f g sq).hom =
      (realizationCylinderIso X).hom ≫ l := by
  simpa [realizedCylinder, ← Category.assoc] using
    congrArg (fun k ↦ (realizationCylinderIso X).hom ≫ k)
      (realizedCylinder_realizationIso f g sq)

/-- Exact formula on the original realized simplicial endpoint leg. -/
@[reassoc (attr := simp)]
theorem realizationIso_ends :
    SSet.toTop.map (simplicialEnds f g) ≫ (realizationIso f g sq).hom =
      (realizationBinarySumIso Y Z).hom ≫ e := by
  simpa [realizedEnds, ← Category.assoc] using
    congrArg (fun k ↦ (realizationBinarySumIso Y Z).hom ≫ k)
      (realizedEnds_realizationIso f g sq)

@[simp] theorem realizationHomeomorph_cylinder (x : |X| ⊗ TopCat.I) :
    realizationHomeomorph f g sq (realizedCylinder f g x) = l x :=
  ConcreteCategory.congr_hom (realizedCylinder_realizationIso f g sq) x

@[simp] theorem realizationHomeomorph_ends (x : |Y| ⊕ |Z|) :
    realizationHomeomorph f g sq (realizedEnds f g x) = e x :=
  ConcreteCategory.congr_hom (realizedEnds_realizationIso f g sq) x

end DoubleCylinder
end TopCat
