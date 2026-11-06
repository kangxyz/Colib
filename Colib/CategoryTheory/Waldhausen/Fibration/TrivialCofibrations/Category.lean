/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Original weak arrows and weak cofibrations

Both categories keep the actual original objects. Their maps are the original
arrows satisfying the displayed predicates. Structural cylinder data contains
only actual functors, maps, identities and preservation properties; no comma
contractibility or homotopical comparison is an input.


Implementation provenance:
`Quillen/Waldhausen/Fibration/TrivialCofibrations/Category.lean`
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

/-- The precise cylinder data used by the weak-cofibration comma construction. -/
structure CylinderData (cof weq : MorphismProperty C) where
  /-- The functor assigning a cylinder middle object to each arrow and maps to commutative
  squares. -/
  middle : Arrow C ⥤ C
  /-- The natural cofibration from the arrow source to its cylinder middle object. -/
  inclusion : Arrow.leftFunc ⟶ middle
  /-- The natural weak equivalence from the cylinder middle object to the arrow target,
  factoring the original arrow through `inclusion`. -/
  projection : middle ⟶ Arrow.rightFunc
  /-- The natural cofibration from the arrow target into the cylinder middle object, which is a
  section of `projection`. -/
  target : Arrow.rightFunc ⟶ middle
  factorization (f : Arrow C) : inclusion.app f ≫ projection.app f = f.hom
  target_projection (f : Arrow C) : target.app f ≫ projection.app f = 𝟙 f.right
  inclusion_cof (f : Arrow C) : cof (inclusion.app f)
  target_cof (f : Arrow C) : cof (target.app f)
  projection_weak (f : Arrow C) : weq (projection.app f)
  middle_cof {f g : Arrow C} (α : f ⟶ g) : cof α.left → cof α.right → cof (middle.map α)

variable (cof weq : MorphismProperty C) [cof.IsMultiplicative] [weq.IsMultiplicative]

/-- The original objects and original weak arrows. -/
abbrev WeakCategory := WideSubcategory weq

/-- The same original objects, with original arrows that are both cofibrations and weak. -/
abbrev CofibrationCategory := WideSubcategory (cof ⊓ weq)

/-- The literal inclusion, unchanged on every original object and underlying arrow. -/
def inclusion : CofibrationCategory cof weq ⥤ WeakCategory weq where
  obj X := ⟨X.obj⟩
  map f := ⟨f.hom, f.property.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem inclusion_obj (X : CofibrationCategory cof weq) :
    ((inclusion cof weq).obj X).obj = X.obj := rfl

@[simp] theorem inclusion_map {X Y : CofibrationCategory cof weq} (f : X ⟶ Y) :
    ((inclusion cof weq).map f).hom = f.hom := rfl

/-- The actual comma category of original weak arrows into a fixed original object. -/
abbrev Over (Y : WeakCategory weq) := CostructuredArrow (inclusion cof weq) Y

variable {cof weq} (D : CylinderData cof weq) [weq.HasTwoOutOfThreeProperty]

omit [cof.IsMultiplicative] [weq.IsMultiplicative] in
/-- The first endpoint is weak whenever the original arrow is weak. -/
theorem CylinderData.inclusion_weak (f : Arrow C) (hf : weq f.hom) : weq (D.inclusion.app f) := by
  apply weq.of_postcomp (W' := weq) _ (D.projection.app f) (D.projection_weak f)
  rw [D.factorization]
  exact hf

omit [cof.IsMultiplicative] in
/-- The actual second endpoint is weak by its proved section identity. -/
theorem CylinderData.target_weak (f : Arrow C) : weq (D.target.app f) := by
  apply weq.of_postcomp (W' := weq) _ (D.projection.app f) (D.projection_weak f)
  rw [D.target_projection]
  exact weq.id_mem _

omit [cof.IsMultiplicative] [weq.IsMultiplicative] in
/-- The original projection proves weakness of a middle square from its right endpoint alone. -/
theorem CylinderData.middle_weak {f g : Arrow C} (α : f ⟶ g) (hα : weq α.right) :
    weq (D.middle.map α) := by
  apply weq.of_postcomp (W' := weq) _ (D.projection.app g) (D.projection_weak g)
  rw [D.projection.naturality]
  exact weq.comp_mem _ _ (D.projection_weak f) hα

end CategoryTheory.Waldhausen.Fibration.TrivialCofibrations
