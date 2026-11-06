/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.TrivialCofibrations.Category

/-! # The genuine cylinder zigzag in the original weak-cofibration comma category

Every original weak arrow X → Y gives the actual projection T(f) → Y.
The two original cylinder endpoints define id → T ← const(Y), with every
map a genuine weak cofibration in the comma category. The construction is
functorial for its original weak-cofibration morphisms.


Implementation provenance:
`Quillen/Waldhausen/Fibration/TrivialCofibrations/CommaCylinder.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.TrivialCofibrations
variable {C : Type u} [Category.{v} C]
  (cof weq : MorphismProperty C) [cof.IsMultiplicative] [weq.IsMultiplicative]

/-- Retain the original weak arrow to the fixed target as an ordinary arrow. -/
def overArrow (Y : WeakCategory weq) : Over cof weq Y ⥤ Arrow C where
  obj F := Arrow.mk F.hom.hom
  map {F G} α := Arrow.homMk α.left.hom (𝟙 Y.obj) (by
    have h := congrArg (fun f ↦ f.hom) (CostructuredArrow.w α)
    change α.left.hom ≫ G.hom.hom = F.hom.hom at h
    change α.left.hom ≫ G.hom.hom = F.hom.hom ≫ 𝟙 Y.obj
    simpa only [Category.comp_id] using h)
  map_id _ := by apply Arrow.hom_ext <;> rfl
  map_comp _ _ := by
    apply Arrow.hom_ext
    · rfl
    · exact (Category.id_comp _).symm

@[simp] theorem overArrow_map_left {Y : WeakCategory weq} {F G : Over cof weq Y} (α : F ⟶ G) :
    ((overArrow cof weq Y).map α).left = α.left.hom := rfl

@[simp] theorem overArrow_map_right {Y : WeakCategory weq} {F G : Over cof weq Y} (α : F ⟶ G) :
    ((overArrow cof weq Y).map α).right = 𝟙 Y.obj := rfl

variable (D : CylinderData cof weq) [weq.HasTwoOutOfThreeProperty] (Y : WeakCategory weq)

/-- The original weak projection is an actual object of the same comma category. -/
def overCylinderObj (F : Over cof weq Y) : Over cof weq Y :=
  CostructuredArrow.mk (Y := (⟨D.middle.obj ((overArrow cof weq Y).obj F)⟩ : CofibrationCategory
    cof weq))
    ⟨D.projection.app ((overArrow cof weq Y).obj F), D.projection_weak _⟩

/-- The actual middle map is a weak-cofibration comma morphism. -/
def overCylinderMap {F G : Over cof weq Y} (α : F ⟶ G) :
    overCylinderObj cof weq D Y F ⟶ overCylinderObj cof weq D Y G :=
  CostructuredArrow.homMk
    ⟨D.middle.map ((overArrow cof weq Y).map α),
      ⟨D.middle_cof _ α.left.property.1 (cof.id_mem _),
        D.middle_weak _ (weq.id_mem _)⟩⟩ (by
      apply WideSubcategory.hom_ext
      change D.middle.map ((overArrow cof weq Y).map α) ≫
        D.projection.app ((overArrow cof weq Y).obj G) = D.projection.app ((overArrow cof weq
          Y).obj F)
      have h := D.projection.naturality ((overArrow cof weq Y).map α)
      change D.middle.map ((overArrow cof weq Y).map α) ≫
        D.projection.app ((overArrow cof weq Y).obj G) =
          D.projection.app ((overArrow cof weq Y).obj F) ≫ 𝟙 Y.obj at h
      exact h.trans (Category.comp_id _))

/-- Genuine comma endofunctor defined by the original cylinder. -/
def overCylinder : Over cof weq Y ⥤ Over cof weq Y where
  obj := overCylinderObj cof weq D Y
  map := overCylinderMap cof weq D Y
  map_id F := by
    apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    change D.middle.map ((overArrow cof weq Y).map (𝟙 F)) = 𝟙 _
    rw [Functor.map_id, Functor.map_id]
  map_comp α β := by
    apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    change D.middle.map ((overArrow cof weq Y).map (α ≫ β)) =
      D.middle.map ((overArrow cof weq Y).map α) ≫ D.middle.map ((overArrow cof weq Y).map β)
    rw [Functor.map_comp, Functor.map_comp]

/-- The original identity of the fixed target is the chosen comma vertex. -/
def overPoint : Over cof weq Y :=
  CostructuredArrow.mk (Y := (⟨Y.obj⟩ : CofibrationCategory cof weq)) (𝟙 Y)

/-- The first original cylinder inclusion gives an actual weak-cofibration comma map. -/
def overInclusion : 𝟭 (Over cof weq Y) ⟶ overCylinder cof weq D Y where
  app F := CostructuredArrow.homMk
    ⟨D.inclusion.app ((overArrow cof weq Y).obj F),
      ⟨D.inclusion_cof _, D.inclusion_weak _ F.hom.property⟩⟩ (by
        apply WideSubcategory.hom_ext
        exact D.factorization _)
  naturality F G α := by
    apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    exact D.inclusion.naturality ((overArrow cof weq Y).map α)

/-- The proved second-endpoint section gives the other actual weak-cofibration comma map. -/
def overTarget : (Functor.const (Over cof weq Y)).obj (overPoint cof weq Y) ⟶
    overCylinder cof weq D Y where
  app F := CostructuredArrow.homMk
    ⟨D.target.app ((overArrow cof weq Y).obj F), ⟨D.target_cof _, D.target_weak _⟩⟩ (by
      apply WideSubcategory.hom_ext
      exact D.target_projection _)
  naturality F G α := by
    apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    exact D.target.naturality ((overArrow cof weq Y).map α)

/-- The first zigzag leg is literally the original cylinder inclusion. -/
@[simp] theorem overInclusion_app (F : Over cof weq Y) :
    ((overInclusion cof weq D Y).app F).left.hom =
      D.inclusion.app (Arrow.mk F.hom.hom) := rfl

/-- The second zigzag leg is literally the original target inclusion. -/
@[simp] theorem overTarget_app (F : Over cof weq Y) :
    ((overTarget cof weq D Y).app F).left.hom = D.target.app (Arrow.mk F.hom.hom) := rfl

end CategoryTheory.Waldhausen.Fibration.TrivialCofibrations
