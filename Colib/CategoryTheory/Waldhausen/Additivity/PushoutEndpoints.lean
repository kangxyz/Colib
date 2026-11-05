/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.PushoutFunctor

/-! # The comparison and identity endpoint of the additivity pushout functor

## Implementation provenance

Adapted from `Quillen/Waldhausen/Additivity/PushoutEndpoints.lean` at commit
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

/-- The map from the actual relative pushout to the middle functor at the target. -/
def comparison (f : Arrow C) : (pushoutFunctor W a ha).obj f ⟶ G.obj f.right := by
  letI := hasPushout W a ha f.hom
  exact pushout.desc (G.map f.hom) (a.app f.right) (a.naturality f.hom).symm

@[reassoc (attr := simp)]
theorem sourceι_comparison (f : Arrow C) :
    sourceι W a ha f ≫ comparison W a ha f = G.map f.hom := by
  let := hasPushout W a ha f.hom
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem targetι_comparison (f : Arrow C) :
    targetι W a ha f ≫ comparison W a ha f = a.app f.right := by
  let := hasPushout W a ha f.hom
  exact pushout.inr_desc _ _ _

/-- The relative-pushout comparison is natural on every commutative square. -/
@[reassoc]
theorem comparison_naturality {f g : Arrow C} (φ : f ⟶ g) :
    (pushoutFunctor W a ha).map φ ≫ comparison W a ha g =
      comparison W a ha f ≫ G.map φ.right := by
  apply (pushoutFunctor_isPushout W a ha f).hom_ext
  · rw [sourceι_naturality_assoc, sourceι_comparison, sourceι_comparison_assoc]
    simp only [← G.map_comp, φ.w]
  · rw [targetι_naturality_assoc, targetι_comparison, targetι_comparison_assoc]
    exact a.naturality φ.right

/-- The canonical natural transformation used in the relative-cofibration condition. -/
def comparisonNatTrans : pushoutFunctor W a ha ⟶ Arrow.rightFunc ⋙ G where
  app := comparison W a ha
  naturality _ _ φ := comparison_naturality W a ha φ

/-- The ordinary identity-arrow embedding. -/
def identityArrow : C ⥤ Arrow C where
  obj X := Arrow.mk (𝟙 X)
  map f := Arrow.homMk f f (by simp)
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

/-- At identity arrows, the source inclusion is invertible by the actual pushout property. -/
theorem sourceι_identity_isIso (X : C) : IsIso (sourceι W a ha (Arrow.mk (𝟙 X))) := by
  let := hasPushout W a ha (𝟙 X)
  change IsIso (pushout.inl (a.app X) (F.map (𝟙 X)))
  infer_instance

/-- The identity endpoint of the pushout deformation is the middle functor. -/
def pushoutIdentityIso (X : C) :
    (pushoutFunctor W a ha).obj (Arrow.mk (𝟙 X)) ≅ G.obj X := by
  letI := sourceι_identity_isIso W a ha X
  exact (asIso (sourceι W a ha (Arrow.mk (𝟙 X)))).symm

@[simp]
theorem pushoutIdentityIso_hom (X : C) :
    (pushoutIdentityIso W a ha X).hom = comparison W a ha (Arrow.mk (𝟙 X)) := by
  let := sourceι_identity_isIso W a ha X
  apply (cancel_epi (sourceι W a ha (Arrow.mk (𝟙 X)))).1
  rw [sourceι_comparison]
  change sourceι W a ha (Arrow.mk (𝟙 X)) ≫ inv (sourceι W a ha (Arrow.mk (𝟙 X))) = G.map (𝟙 X)
  rw [IsIso.hom_inv_id, G.map_id]
  rfl

/-- The endpoint identification is an actual natural isomorphism of functors. -/
def pushoutIdentityNatIso : identityArrow ⋙ pushoutFunctor W a ha ≅ G :=
  NatIso.ofComponents (pushoutIdentityIso W a ha) (by
    intro X Y f
    simp only [Functor.comp_map, pushoutIdentityIso_hom]
    exact comparison_naturality W a ha (identityArrow.map f))

/-- The standard structural cofibration condition on a natural transformation.
It asks that the actual relative pushout map be a cofibration, never for an
additivity or K-theory equivalence conclusion. -/
structure IsCofibrationTransformation (V : Structure C) : Prop where
  app_cof (X : C) : W.cof (a.app X)
  relative_cof {X Y : C} (f : X ⟶ Y) : V.cof f →
    W.cof (comparison W a app_cof (Arrow.mk f))

end CategoryTheory.Waldhausen.Additivity
