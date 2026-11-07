/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Adjunction.Comma

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/FiberedCategory/CocartesianComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Strict fibers and comma categories via cocartesian lifts -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Fiber
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) (b : D)

/-- The original inclusion of the strict fiber into the costructured comma category. -/
def toCostructured : F.Fiber b ⥤ CostructuredArrow F b where
  obj X := CostructuredArrow.mk (eqToHom X.2)
  map {X Y} f := CostructuredArrow.homMk f.val (by
    let := f.property
    simp [IsHomLift.fac' F (𝟙 b) f.val])
  map_id X := by apply CostructuredArrow.hom_ext; rfl
  map_comp f g := by apply CostructuredArrow.hom_ext; rfl

variable (U : CostructuredArrow F b) (x : C) (hx : F.obj x = b)
variable (f : U.left ⟶ x) [F.IsCocartesian U.hom f]

/-- The actual universal arrow determined by a cocartesian lift. -/
def cocartesianLiftArrow : U ⟶ (toCostructured F b).obj ⟨x, hx⟩ :=
  CostructuredArrow.homMk f (by
    change F.map f ≫ eqToHom hx = U.hom
    simp [IsHomLift.fac' F U.hom f])

/-- Cocartesian factorization is precisely factorization in the strict fiber. -/
theorem existsUnique_cocartesianFactor (X : F.Fiber b)
    (a : U ⟶ (toCostructured F b).obj X) :
    ∃! h : (Functor.Fiber.mk hx : F.Fiber b) ⟶ X,
      cocartesianLiftArrow F b U x hx f ≫ (toCostructured F b).map h = a := by
  let : F.IsHomLift U.hom a.left :=
    IsHomLift.of_commsq F U.hom a.left rfl X.2 (by
      have ha := a.w
      change F.map a.left ≫ eqToHom X.2 = U.hom at ha
      simpa only [eqToHom_refl, Category.id_comp] using ha)
  obtain ⟨k, hk, hu⟩ := Functor.IsCocartesian.universal_property
    (p := F) (f := U.hom) (φ := f) a.left
  refine ⟨⟨k, hk.1⟩, ?_, ?_⟩
  · apply CostructuredArrow.hom_ext
    exact hk.2
  · intro h hh
    apply Subtype.ext
    exact hu h.val ⟨h.property, congrArg (fun t => t.left) hh⟩

/-- The chosen cocartesian lift is initial among arrows to the strict fiber. -/
def cocartesianLiftIsInitial :
    IsInitial (StructuredArrow.mk (cocartesianLiftArrow F b U x hx f)) := by
  let P := fun (A : StructuredArrow U (toCostructured F b)) =>
    existsUnique_cocartesianFactor F b U x hx f A.right A.hom
  let k := fun A => (P A).choose
  have hk : ∀ A, cocartesianLiftArrow F b U x hx f ≫ (toCostructured F b).map (k A) =
      A.hom := fun A => (P A).choose_spec.1
  refine IsInitial.ofUniqueHom (fun A => StructuredArrow.homMk (k A) (hk A)) ?_
  intro A h
  apply StructuredArrow.hom_ext
  exact (P A).choose_spec.2 h.right (by simpa using h.w)

/-- Actual cocartesian lifts make the strict-fiber inclusion a right adjoint. -/
theorem toCostructured_isRightAdjoint_of_lifts
    (lifts : ∀ U : CostructuredArrow F b,
      ∃ (x : C) (_hx : F.obj x = b) (f : U.left ⟶ x), F.IsCocartesian U.hom f) :
    (toCostructured F b).IsRightAdjoint := by
  let : ∀ U : CostructuredArrow F b, HasInitial (StructuredArrow U (toCostructured F b)) := by
    intro U
    obtain ⟨x, hx, f, hf⟩ := lifts U
    let := hf
    exact (cocartesianLiftIsInitial F b U x hx f).hasInitial
  exact isRightAdjointOfStructuredArrowInitials _

end CategoryTheory.Fiber
