/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyCofiber.ReducedMappingCone
public import Colib.Topology.DoubleMappingCylinder.BaseLineHEP
public import Colib.Topology.DoubleMappingCylinder.Basic
public import Colib.Topology.Pushout.HomotopyEquivalence

/-!
# The genuine reduction map from the ordinary cone to the based cone

The original reduced mapping-cone quotient is the pushout collapsing the actual chosen-point
interval in the ordinary double-cylinder cone. Well-based source and target points make this
literal collapse a homotopy equivalence. No weak-equivalence inverse is selected.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyCofiber/ReducedMappingConeCollapse.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original objects, maps,
point hypotheses, whole stored cylinder paths and universe parameters are
retained. Native namespace and lower-import ownership are used. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace Topology.ReducedMappingCone

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀)

/-- The actual ordinary cone before its chosen-point interval is collapsed. -/
abbrev UnreducedSpace := TopCat.DoubleCylinder.Cylinder (TopCat.ofHom f)
  (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))

/-- The actual unreduced cylinder inclusion, retaining its full interval coordinate. -/
abbrev unreducedCylinder : TopCat.of X ⊗ TopCat.I ⟶ UnreducedSpace f :=
  TopCat.DoubleCylinder.cylinderLine (TopCat.ofHom f)
    (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))

/-- The two unreduced cone ends are the original target and a single vertex. -/
abbrev unreducedEnd : TopCat.of (Y ⊕ PUnit.{u + 1}) ⟶ UnreducedSpace f :=
  TopCat.DoubleCylinder.cylinderEnd (TopCat.ofHom f)
    (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))

/-- The original unreduced cone is the actual endpoint-attachment pushout. -/
theorem unreducedSquare : IsPushout (TopCat.intervalEndpoints (TopCat.of X))
    (TopCat.DoubleCylinder.endMap (TopCat.ofHom f)
      (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1}))))
    (unreducedCylinder f) (unreducedEnd f) := TopCat.DoubleCylinder.cylinderSquare _ _

/-- Collapse the literal base interval in the ordinary cone to the original reduced cone point. -/
def reduction : UnreducedSpace f ⟶ TopCat.of (Space x₀ y₀ f) :=
  (unreducedSquare f).desc
    (TopCat.ofHom ⟨fun z : X × TopCat.I ↦ cylinder x₀ y₀ f (z.2.down, z.1), by fun_prop⟩)
    (TopCat.ofHom ⟨Sum.elim (inr x₀ y₀ f) (fun _ ↦ point x₀ y₀ f),
      (inr x₀ y₀ f).continuous.sumElim continuous_const⟩)
    (by
      ext x : 1
      cases x with
      | inl x => exact cylinder_zero x₀ y₀ f x
      | inr x => exact cylinder_one x₀ y₀ f x)

@[simp] theorem reduction_cylinder (x : X) (t : TopCat.I) :
    reduction x₀ y₀ f (unreducedCylinder f (x, t)) = cylinder x₀ y₀ f (t.down, x) :=
  ConcreteCategory.congr_hom ((unreducedSquare f).inl_desc _ _ _) (x, t)

@[simp] theorem reduction_end (z : Y ⊕ PUnit.{u + 1}) :
    reduction x₀ y₀ f (unreducedEnd f z) =
      Sum.elim (inr x₀ y₀ f) (fun _ ↦ point x₀ y₀ f) z :=
  ConcreteCategory.congr_hom ((unreducedSquare f).inr_desc _ _ _) z

/-- The constant map identifies all values of the base interval. -/
abbrev intervalToPoint : TopCat.I ⟶ TopCat.of PUnit.{u + 1} :=
  TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

/-- The singleton map selects the unchanged reduced cone point. -/
abbrev reducedPoint : TopCat.of PUnit.{u + 1} ⟶ TopCat.of (Space x₀ y₀ f) :=
  TopCat.ofHom (ContinuousMap.const _ (point x₀ y₀ f))

/-- The literal chosen-point interval is collapsed by the reduction map. -/
theorem reduction_square :
    TopCat.DoubleCylinder.baseLine (l := unreducedCylinder f) x₀ ≫ reduction x₀ y₀ f =
      intervalToPoint ≫ reducedPoint x₀ y₀ f := by
  ext t
  exact (reduction_cylinder x₀ y₀ f x₀ t).trans (cylinder_base x₀ y₀ f t.down)

include hf in
/-- The original reduced quotient is exactly the pushout collapsing the original base interval. -/
theorem reduction_isPushout :
    IsPushout (TopCat.DoubleCylinder.baseLine (l := unreducedCylinder f) x₀) intervalToPoint
      (reduction x₀ y₀ f) (reducedPoint x₀ y₀ f) := by
  have hl (x : X) : unreducedCylinder f (x, (0 : TopCat.I)) = unreducedEnd f (Sum.inl (f x)) :=
    ConcreteCategory.congr_hom (unreducedSquare f).w (Sum.inl x)
  have hr (x : X) : unreducedCylinder f (x, (1 : TopCat.I)) =
      unreducedEnd f (Sum.inr PUnit.unit) :=
    ConcreteCategory.congr_hom (unreducedSquare f).w (Sum.inr x)
  let coc := PushoutCocone.mk _ _ (reduction_square x₀ y₀ f)
  apply IsPushout.of_isColimit (c := coc)
  let lift (s : PushoutCocone (TopCat.DoubleCylinder.baseLine (l := unreducedCylinder f) x₀)
      intervalToPoint) : TopCat.of (Space x₀ y₀ f) ⟶ s.pt := by
    have hb (t : TopCat.I) : s.inl (unreducedCylinder f (x₀, t)) = s.inr PUnit.unit :=
      ConcreteCategory.congr_hom s.condition t
    have hb₀ : s.inl (unreducedEnd f (Sum.inl y₀)) = s.inr PUnit.unit := by
      rw [← hf, ← hl]
      exact hb 0
    exact TopCat.ofHom (desc x₀ y₀ f
      ⟨fun y ↦ s.inl (unreducedEnd f (Sum.inl y)), by fun_prop⟩
      ⟨fun z ↦ s.inl (unreducedCylinder f (z.2, ULift.up z.1)), by fun_prop⟩
      (fun x ↦ congrArg s.inl (hl x))
      (fun x ↦ (congrArg s.inl ((hr x).trans (hr x₀).symm)).trans ((hb 1).trans hb₀.symm))
      (fun t ↦ (hb (ULift.up t)).trans hb₀.symm))
  have hleft (s) : reduction x₀ y₀ f ≫ lift s = s.inl := by
    apply (unreducedSquare f).hom_ext
    · ext ⟨x, t⟩
      change lift s (reduction x₀ y₀ f (unreducedCylinder f (x, t))) = _
      rw [reduction_cylinder]
      rfl
    · ext z
      change lift s (reduction x₀ y₀ f (unreducedEnd f z)) = _
      rw [reduction_end]
      cases z with
      | inl y => rfl
      | inr z =>
        have hb (t : TopCat.I) : s.inl (unreducedCylinder f (x₀, t)) = s.inr PUnit.unit :=
          ConcreteCategory.congr_hom s.condition t
        change s.inl (unreducedEnd f (Sum.inl y₀)) = s.inl (unreducedEnd f (Sum.inr z))
        rw [← hf, ← hl, ← hr x₀]
        exact (hb 0).trans (hb 1).symm
  have hright (s) : reducedPoint x₀ y₀ f ≫ lift s = s.inr := by
    ext z
    change s.inl (unreducedEnd f (Sum.inl y₀)) = s.inr z
    rw [← hf, ← hl]
    exact ConcreteCategory.congr_hom s.condition (0 : TopCat.I)
  refine PushoutCocone.IsColimit.mk _ lift hleft hright ?_
  intro s m hm _
  apply TopCat.hom_ext
  apply hom_ext
  · intro y
    have he := ConcreteCategory.congr_hom hm (unreducedEnd f (Sum.inl y))
    change m (reduction x₀ y₀ f (unreducedEnd f (Sum.inl y))) = _ at he
    rw [reduction_end] at he
    exact he
  · intro ⟨t, x⟩
    have he := ConcreteCategory.congr_hom hm (unreducedCylinder f (x, ULift.up t))
    change m (reduction x₀ y₀ f (unreducedCylinder f (x, ULift.up t))) = _ at he
    rw [reduction_cylinder] at he
    exact he

/-- Genuine HEP of both specified points makes the actual cone-reduction map a homotopy
 equivalence. The forward map is the original quotient reduction. -/
def reductionHomotopyEquiv
    (hX : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)))
    (hY : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀))) :
    ContinuousMap.HomotopyEquiv (UnreducedSpace f) (Space x₀ y₀ f) := by
  have hP : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (PUnit.unit : PUnit.{u + 1}))) := by
    have he : TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (PUnit.unit : PUnit.{u + 1})) =
        (𝟙 (TopCat.of PUnit.{u + 1})) := by ext x
    rw [he]
    exact TopCat.homotopyExtensionProperty_of_isIso _
  have hline := TopCat.DoubleCylinder.homotopyExtensionProperty_baseLine
    (TopCat.ofHom f) (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))
    (unreducedSquare f) x₀ y₀ PUnit.unit hf rfl hX hY hP
  let e : ContinuousMap.HomotopyEquiv TopCat.I PUnit.{u + 1} :=
    { toFun := ContinuousMap.const _ PUnit.unit
      invFun := ContinuousMap.const _ 0
      left_inv := ⟨{
        toFun := fun z ↦ ULift.up (z.1 * z.2.down)
        continuous_toFun := by
          apply Continuous.comp continuous_uliftUp
          apply Continuous.subtype_mk
          exact (continuous_subtype_val.comp continuous_fst).mul
            (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd))
        map_zero_left := fun t ↦ by
          change ULift.up ((0 : unitInterval) * t.down) = (0 : TopCat.I)
          simp only [zero_mul]
          rfl
        map_one_left := fun t ↦ by
          change ULift.up ((1 : unitInterval) * t.down) = t
          simp only [one_mul]
          rfl }⟩
      right_inv := by
        have he : (ContinuousMap.const TopCat.I (PUnit.unit : PUnit.{u + 1})).comp
            (ContinuousMap.const PUnit.{u + 1} (0 : TopCat.I)) = ContinuousMap.id _ := by ext x
        rw [he] }
  exact TopCat.Pushout.pushoutHomotopyEquivAlongCofibration (reduction_isPushout x₀ y₀ f hf)
    hline e (by ext t)

@[simp] theorem reductionHomotopyEquiv_toFun
    (hX : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)))
    (hY : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀))) :
    (reductionHomotopyEquiv x₀ y₀ f hf hX hY).toFun = (reduction x₀ y₀ f).hom := rfl

include hf in
/-- The actual reduced cone point has HEP when the two original points do. -/
theorem point_homotopyExtensionProperty
    (hX : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)))
    (hY : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀))) :
    TopCat.HomotopyExtensionProperty (reducedPoint x₀ y₀ f) := by
  have hP : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (PUnit.unit : PUnit.{u + 1}))) := by
    have he : TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (PUnit.unit : PUnit.{u + 1})) =
        (𝟙 (TopCat.of PUnit.{u + 1})) := by ext x
    rw [he]
    exact TopCat.homotopyExtensionProperty_of_isIso _
  exact TopCat.homotopyExtensionProperty_pushout (reduction_isPushout x₀ y₀ f hf)
    (TopCat.DoubleCylinder.homotopyExtensionProperty_baseLine
      (TopCat.ofHom f) (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))
      (unreducedSquare f) x₀ y₀ PUnit.unit hf rfl hX hY hP)

end Topology.ReducedMappingCone
