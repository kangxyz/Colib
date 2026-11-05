/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The actual pushout functor used in the additivity deformation

For a pointwise cofibration `a : F ⟶ G`, an arrow `f : X ⟶ Y` is sent to
`G X ⨿[F X] F Y`. The construction uses genuine categorical pushouts and is
functorial on all commutative squares. The Waldhausen gluing axiom proves
preservation of pointwise weak equivalences. No additivity conclusion is an
input to this construction.


## Implementation provenance

Adapted from `Quillen/Waldhausen/Additivity/PushoutFunctor.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original objects, maps,
universes and hypotheses are retained. This categorical input is not an
additivity theorem on realizations or K-groups.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v'

namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (ha : ∀ X, W.cof (a.app X))
include W ha

/-- Every required pushout exists by the pointwise cofibration hypothesis. -/
theorem hasPushout {X Y : C} (f : X ⟶ Y) : HasPushout (a.app X) (F.map f) := by
  obtain ⟨P, g, j, h⟩ := W.pushout_exists (a.app X) (F.map f) (ha X)
  exact h.hasPushout

/-- The genuine arrow-category pushout functor. -/
def pushoutFunctor : Arrow C ⥤ D := by
  letI {X Y : C} (f : X ⟶ Y) : HasPushout (a.app X) (F.map f) :=
    hasPushout W a ha f
  exact {
    obj f := pushout (a.app f.left) (F.map f.hom)
    map {f g} φ := pushout.map (a.app f.left) (F.map f.hom)
      (a.app g.left) (F.map g.hom) (G.map φ.left) (F.map φ.right) (F.map φ.left)
      (a.naturality φ.left).symm (by simp only [← F.map_comp, φ.w])
    map_id f := by
      apply pushout.hom_ext <;> simp
    map_comp φ ψ := by
      apply pushout.hom_ext <;> simp [Category.assoc] }

/-- The source-middle inclusion into the actual pushout. -/
def sourceι (f : Arrow C) : G.obj f.left ⟶ (pushoutFunctor W a ha).obj f := by
  letI := hasPushout W a ha f.hom
  exact pushout.inl _ _

/-- The target-subobject inclusion into the actual pushout. -/
def targetι (f : Arrow C) : F.obj f.right ⟶ (pushoutFunctor W a ha).obj f := by
  letI := hasPushout W a ha f.hom
  exact pushout.inr _ _

@[reassoc (attr := simp)]
theorem sourceι_naturality {f g : Arrow C} (φ : f ⟶ g) :
    sourceι W a ha f ≫ (pushoutFunctor W a ha).map φ =
      G.map φ.left ≫ sourceι W a ha g := by
  let {X Y : C} (f : X ⟶ Y) : HasPushout (a.app X) (F.map f) :=
    hasPushout W a ha f
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem targetι_naturality {f g : Arrow C} (φ : f ⟶ g) :
    targetι W a ha f ≫ (pushoutFunctor W a ha).map φ =
      F.map φ.right ≫ targetι W a ha g := by
  let {X Y : C} (f : X ⟶ Y) : HasPushout (a.app X) (F.map f) :=
    hasPushout W a ha f
  exact pushout.inr_desc _ _ _

/-- The displayed legs satisfy the pushout square, with its full universal property. -/
theorem pushoutFunctor_isPushout (f : Arrow C) :
    IsPushout (a.app f.left) (F.map f.hom) (sourceι W a ha f) (targetι W a ha f) := by
  let := hasPushout W a ha f.hom
  exact IsPushout.of_hasPushout _ _

/-- The target leg is a genuine cofibration. -/
theorem targetι_cof (f : Arrow C) : W.cof (targetι W a ha f) :=
  W.cof_pushout (ha _) (pushoutFunctor_isPushout W a ha f)

/-- Gluing proves that the pushout functor preserves pointwise weak squares. -/
theorem pushoutFunctor_map_weak {f g : Arrow C} (φ : f ⟶ g)
    (h₀ : W.weq (F.map φ.left)) (h₁ : W.weq (G.map φ.left))
    (h₂ : W.weq (F.map φ.right)) :
    W.weq ((pushoutFunctor W a ha).map φ) :=
  W.gluing (F.map φ.left) (G.map φ.left) (F.map φ.right)
    ((pushoutFunctor W a ha).map φ) (ha _) (ha _)
    (pushoutFunctor_isPushout W a ha f) (pushoutFunctor_isPushout W a ha g)
    (a.naturality φ.left).symm (by simp only [← F.map_comp, φ.w])
    (sourceι_naturality W a ha φ) (targetι_naturality W a ha φ) h₀ h₁ h₂

end CategoryTheory.Waldhausen.Additivity
