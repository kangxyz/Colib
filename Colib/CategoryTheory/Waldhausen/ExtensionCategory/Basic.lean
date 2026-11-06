/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.PushoutCofibrations
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The category of actual cofibration arrows

Objects are genuine cofibrations. Weak equivalences are componentwise, and
cofibrations use the source-plus-relative-target (Reedy) condition.


Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/Basic.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The predicate selecting arrows whose underlying map is a cofibration in `W`. -/
def objects : ObjectProperty (Arrow C) := fun f ↦ W.cof f.hom
/-- The full subcategory of `Arrow C` consisting of cofibration arrows. -/
abbrev Obj := (objects W).FullSubcategory

/-- The full-subcategory inclusion that forgets the cofibration condition on an arrow. -/
def forget : Obj W ⥤ Arrow C := (objects W).ι
instance forget_full : (forget W).Full := by unfold forget; infer_instance
instance forget_faithful : (forget W).Faithful := by unfold forget; infer_instance

/-- The functor evaluating a cofibration arrow at its source object. -/
def source : Obj W ⥤ C := forget W ⋙ Arrow.leftFunc
/-- The functor evaluating a cofibration arrow at its target object, the middle term of the
associated extension. -/
def middle : Obj W ⥤ C := forget W ⋙ Arrow.rightFunc

/-- The original cofibration is the structural source-to-middle transformation. -/
def inclusion : source W ⟶ middle W := Functor.whiskerLeft (forget W) Arrow.leftToRight

theorem inclusion_cof (X : Obj W) : W.cof ((inclusion W).app X) := X.property

/-- The actual relative pushout associated to a square of cofibration arrows. -/
abbrev relativeFunctor : Arrow (Obj W) ⥤ C :=
  Additivity.pushoutFunctor W (inclusion W) (inclusion_cof W)

/-- The canonical map from the pushout of the source-target square of `f` to the target object
of `Y`; this is the relative target map in the Reedy cofibration condition. -/
abbrev relativeMap {X Y : Obj W} (f : X ⟶ Y) :
    (relativeFunctor W).obj (Arrow.mk f) ⟶ (middle W).obj Y :=
  Additivity.comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)

/-- The standard Reedy cofibration condition on an actual commutative square. -/
def cof : MorphismProperty (Obj W) := fun _ _ f ↦
  W.cof ((source W).map f) ∧ W.cof (relativeMap W f)

/-- Weak equivalences are exactly weak equivalences on both components. -/
def weq : MorphismProperty (Obj W) :=
  W.weq.inverseImage (source W) ⊓ W.weq.inverseImage (middle W)

instance weq_multiplicative : (weq W).IsMultiplicative := by unfold weq; infer_instance

/-- Every Reedy cofibration is also a cofibration on target objects. -/
theorem cof_middle {X Y : Obj W} {f : X ⟶ Y} (hf : cof W f) : W.cof ((middle W).map f) := by
  have hi := W.cof_pushout hf.1
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk f)).flip
  have h := W.cof.comp_mem _ _ hi hf.2
  simpa only [Additivity.sourceι_comparison] using! h

/-- Identity squares satisfy the genuine relative condition. -/
theorem cof_id (X : Obj W) : cof W (𝟙 X) := by
  refine ⟨?_, ?_⟩
  · simpa only [CategoryTheory.Functor.map_id] using W.cof.id_mem ((source W).obj X)
  · have h := W.cof_iso _ (inferInstance : IsIso
      (Additivity.pushoutIdentityIso W (inclusion W) (inclusion_cof W) X).hom)
    simpa only [Additivity.pushoutIdentityIso_hom] using h

/-- Composition of relative cofibrations follows by a genuine source-change pushout. -/
theorem cof_comp {X Y Z : Obj W} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : cof W f) (hg : cof W g) : cof W (f ≫ g) := by
  refine ⟨?_, ?_⟩
  · simpa only [Functor.map_comp] using W.cof.comp_mem _ _ hf.1 hg.1
  · have h₁ := W.cof_pushout hf.2
      (Additivity.precompose_isPushout W (inclusion W) (inclusion_cof W) f g)
    have h₂ := W.cof.comp_mem _ _ h₁ hg.2
    have h := Additivity.comparison_naturality W (inclusion W) (inclusion_cof W)
      (Additivity.precomposeArrow f g)
    change (relativeFunctor W).map (Additivity.precomposeArrow f g) ≫ relativeMap W g =
      relativeMap W (f ≫ g) ≫ (middle W).map (𝟙 Z) at h
    rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
    rwa [h] at h₂

instance cof_multiplicative : (cof W).IsMultiplicative where
  id_mem := cof_id W
  comp_mem := cof_comp W

/-- Isomorphism squares satisfy the relative condition by actual pushout invariance. -/
theorem cof_iso : MorphismProperty.isomorphisms (Obj W) ≤ cof W := by
  intro X Y f hf
  let : IsIso f := hf
  refine ⟨W.cof_iso _ (inferInstance : IsIso ((source W).map f)), ?_⟩
  let s := Additivity.sourceι W (inclusion W) (inclusion_cof W) (Arrow.mk f)
  let : IsIso ((source W).map (Arrow.mk f).hom) := inferInstanceAs (IsIso ((source W).map f))
  let : IsIso s :=
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk
      f)).isIso_inl_of_isIso
  have h : relativeMap W f = inv s ≫ (middle W).map f := by
    apply (cancel_epi s).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)
  rw [h]
  exact W.cof_iso _ (inferInstance : IsIso (inv s ≫ (middle W).map f))

theorem weq_iso : MorphismProperty.isomorphisms (Obj W) ≤ weq W := by
  intro X Y f hf
  let : IsIso f := hf
  exact ⟨W.weq_iso _ (inferInstance : IsIso ((source W).map f)),
    W.weq_iso _ (inferInstance : IsIso ((middle W).map f))⟩

/-- The literal identity of the chosen zero object is an actual cofibration arrow. -/
def zero : Obj W := ⟨Arrow.mk (𝟙 W.zero), W.cof.id_mem _⟩

/-- The morphism from a cofibration arrow to the chosen zero arrow, given by the unique maps to
the zero object on both components. -/
def toZero (X : Obj W) : X ⟶ zero W :=
  (objects W).homMk (Arrow.homMk (W.isZero.from_ X.obj.left) (W.isZero.from_ X.obj.right)
    (W.isZero.eq_of_tgt _ _))

/-- The morphism from the chosen zero arrow to a cofibration arrow, given by the unique maps
from the zero object on both components. -/
def fromZero (X : Obj W) : zero W ⟶ X :=
  (objects W).homMk (Arrow.homMk (W.isZero.to_ X.obj.left) (W.isZero.to_ X.obj.right)
    (W.isZero.eq_of_src _ _))

/-- The chosen identity arrow is genuinely a zero object in the full arrow category. -/
theorem isZero : IsZero (zero W) where
  unique_to X := by
    refine ⟨{ default := fromZero W X, uniq := ?_ }⟩
    intro f
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> exact W.isZero.eq_of_src _ _
  unique_from X := by
    refine ⟨{ default := toZero W X, uniq := ?_ }⟩
    intro f
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> exact W.isZero.eq_of_tgt _ _

/-- Every actual cofibration arrow is cofibrant for the Reedy condition. -/
theorem cof_fromZero (X : Obj W) : cof W (fromZero W X) := by
  refine ⟨W.cof_zero X.obj.left, ?_⟩
  let t := Additivity.targetι W (inclusion W) (inclusion_cof W) (Arrow.mk (fromZero W X))
  let : IsIso ((inclusion W).app (zero W)) := inferInstanceAs (IsIso (𝟙 W.zero))
  let : IsIso ((inclusion W).app (Arrow.mk (fromZero W X)).left) :=
    inferInstanceAs (IsIso (𝟙 W.zero))
  let : IsIso t :=
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W)
      (Arrow.mk (fromZero W X))).isIso_inr_of_isIso
  have ht : relativeMap W (fromZero W X) = inv t ≫ (inclusion W).app X := by
    apply (cancel_epi t).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk (fromZero W X))
  rw [ht]
  exact W.cof.comp_mem _ _ (W.cof_iso _ (inferInstance : IsIso (inv t))) X.property

end CategoryTheory.Waldhausen.ExtensionCategory
