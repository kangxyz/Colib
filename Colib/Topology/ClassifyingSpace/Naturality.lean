/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.Constant
public import Colib.Topology.ClassifyingSpace.ArrowPaths
public import Colib.Topology.Realization.HomotopyBridge

/-!
# Naturality of realized transformations

Implementation source: `Quillen/CategoryTheory/TheoremB/Naturality.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual simplex families,
path coordinates, and endpoint data are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology CategoryTheory SSet Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory

/-- The categorical nerve-cylinder construction commutes with precomposition. -/
theorem naturalTransformationNerveCylinder_whiskerLeft
    {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]
    (K : A ⥤ C) {F G : C ⥤ D} (α : F ⟶ G) :
    naturalTransformationNerveCylinder (Functor.whiskerLeft K α) =
      nerveMap K ▷ Δ[1] ≫ naturalTransformationNerveCylinder α := by
  have hc : naturalTransformationCylinderFunctor (Functor.whiskerLeft K α) =
      (𝟭 (Fin 2)).prod K ⋙ naturalTransformationCylinderFunctor α := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ rfl rfl ?_
    ext a
    simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
      ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (Functor.whiskerLeft K α) =
    _ ⋙ naturalTransformationCylinderFunctor α
  rw [hc]
  rfl

/-- The categorical nerve-cylinder construction commutes with postcomposition. -/
theorem naturalTransformationNerveCylinder_whiskerRight
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    {F G : C ⥤ D} (α : F ⟶ G) (K : D ⥤ E) :
    naturalTransformationNerveCylinder (Functor.whiskerRight α K) =
      naturalTransformationNerveCylinder α ≫ nerveMap K := by
  have hc : naturalTransformationCylinderFunctor (Functor.whiskerRight α K) =
      naturalTransformationCylinderFunctor α ⋙ K := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ ?_ ?_ ?_
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁]
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁]
    · ext a
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (Functor.whiskerRight α K) =
    (_ ⋙ naturalTransformationCylinderFunctor α) ⋙ K
  rw [hc]
  rfl

/-- Precomposing a natural transformation precomposes its actual realized homotopy. -/
theorem classifyingSpaceNaturalTransformationHomotopy_whiskerLeft
    {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]
    (K : A ⥤ C) {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerLeft K α) (t, x) =
      classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpaceMap K x) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (Functor.whiskerLeft K α))
    ((realizationCylinderIso (nerve A)).inv (x, ULift.up t)) = _
  rw [naturalTransformationNerveCylinder_whiskerLeft, Functor.map_comp, TopCat.comp_app]
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (nerveMap K)) (x, ULift.up t)
  exact congrArg (SSet.toTop.map (naturalTransformationNerveCylinder α)) hn

/-- Postcomposing a natural transformation postcomposes its actual realized homotopy. -/
theorem classifyingSpaceNaturalTransformationHomotopy_whiskerRight
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    {F G : C ⥤ D} (α : F ⟶ G) (K : D ⥤ E)
    (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerRight α K) (t, x) =
      classifyingSpaceMap K (classifyingSpaceNaturalTransformationHomotopy α (t, x)) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (Functor.whiskerRight α K))
    ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) = _
  rw [naturalTransformationNerveCylinder_whiskerRight, Functor.map_comp, TopCat.comp_app]
  rfl

/-- The realized natural-transformation homotopy traverses its component edge
at every object vertex. -/
theorem classifyingSpaceNaturalTransformationHomotopy_vertex_general
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (t : unitInterval) :
    classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpacePoint c) =
      classifyingSpacePath (α.app c) t := by
  let q := (realizationCylinderIso (Δ[0] : SSet.{max u v})).inv (default, ULift.up t)
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (nerveVertexMap c)) (default, ULift.up t)
  change SSet.toTop.map (nerveVertexMap c ▷ Δ[1]) q =
    (realizationCylinderIso (nerve C)).inv (classifyingSpacePoint c, ULift.up t) at hn
  change SSet.toTop.map (naturalTransformationNerveCylinder α)
    ((realizationCylinderIso (nerve C)).inv (classifyingSpacePoint c, ULift.up t)) = _
  rw [← hn]
  change (SSet.toTop.map (nerveVertexMap c ▷ Δ[1]) ≫
    SSet.toTop.map (naturalTransformationNerveCylinder α)) q = _
  rw [← Functor.map_comp, naturalTransformationNerveCylinder_vertex, Functor.map_comp,
    TopCat.comp_app]
  have hs : SSet.toTop.map (snd (Δ[0] : SSet.{max u v}) Δ[1]) q = realizationInterval t := by
    have hh := congrArg _root_.Prod.snd (ConcreteCategory.congr_hom
      (realizationCylinderIso (Δ[0] : SSet.{max u v})).inv_hom_id (default, ULift.up t))
    change SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (snd (Δ[0] : SSet.{max u v}) Δ[1]) q) = ULift.up t at hh
    apply (TopCat.homeoOfIso SSet.stdSimplex.toTopObjIsoI).injective
    exact hh.trans (ConcreteCategory.congr_hom SSet.stdSimplex.toTopObjIsoI.inv_hom_id _).symm
  rw [hs]
  rfl

/-- The original common-universe vertex-track interface is retained. -/
theorem classifyingSpaceNaturalTransformationHomotopy_vertex
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (t : unitInterval) :
    classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpacePoint c) =
      classifyingSpacePath (α.app c) t :=
  classifyingSpaceNaturalTransformationHomotopy_vertex_general α c t

end CategoryTheory
