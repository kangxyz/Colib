/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.AllWeak.Basic

/-! # The original all-acyclic full category is exactly the original category

The actual inclusion and the actual lift `X ↦ ⟨X, trivial⟩` form an exact
equivalence for the inherited fine weak class, preserving both chosen zeros.
No realization or double-S transport is built into this categorical result.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AllWeak/AcyclicEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.AllWeak
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Add only the proved all-weak acyclicity witness to the original object. -/
def acyclicLift : C ⥤ AcyclicCategory (nested W) where
  obj X := ⟨X, trivial⟩
  map f := (acyclicObjects (nested W)).homMk f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem acyclicLift_obj (X : C) : ((acyclicLift W).obj X).obj = X := rfl
@[simp] theorem acyclicLift_map {X Y : C} (f : X ⟶ Y) :
    ((acyclicLift W).map f).hom = f := rfl

/-- Forgetting the witness gives the unchanged original functor. -/
@[simp] theorem acyclicLift_inclusion :
    acyclicLift W ⋙ acyclicInclusion (nested W) = 𝟭 C := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Reinserting the proposition witness retains the original full-category object. -/
@[simp] theorem acyclicInclusion_lift :
    acyclicInclusion (nested W) ⋙ acyclicLift W = 𝟭 (AcyclicCategory (nested W)) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The exact presentation equivalence has the actual original inclusion as forward functor. -/
def acyclicEquivalence : AcyclicCategory (nested W) ≌ C :=
  CategoryTheory.Equivalence.mk (acyclicInclusion (nested W)) (acyclicLift W)
    (eqToIso (acyclicInclusion_lift W).symm) (eqToIso (acyclicLift_inclusion W))

/-- The inverse lift preserves the original fine structure, with genuine pushouts. -/
theorem acyclicLift_exact : IsExact W.cof W.weq
    (acyclicStructure (nested W)).cof (acyclicStructure (nested W)).weq (acyclicLift W) where
  zero h := IsZero.of_full_of_faithful_of_isZero (acyclicObjects (nested W)).ι _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := IsPushout.of_map_of_faithful (acyclicObjects (nested W)).ι h

/-- The forward exact functor remains the original fine acyclic inclusion. -/
theorem acyclicEquivalence_functor_exact : IsExact
    (acyclicStructure (nested W)).cof (acyclicStructure (nested W)).weq
      W.cof W.weq (acyclicEquivalence W).functor := acyclicInclusion_exact (nested W)

@[simp] theorem acyclicLift_zero :
    (acyclicLift W).obj W.zero = (acyclicStructure (nested W)).zero := rfl

@[simp] theorem acyclicEquivalence_zero :
    (acyclicEquivalence W).functor.obj (acyclicStructure (nested W)).zero = W.zero := rfl

/-- Neither direction changes the actual fine weak-equivalence predicate. -/
@[simp] theorem acyclicLift_weak_iff {X Y : C} (f : X ⟶ Y) :
    (acyclicStructure (nested W)).weq ((acyclicLift W).map f) ↔ W.weq f := Iff.rfl

@[simp] theorem acyclicLift_cof_iff {X Y : C} (f : X ⟶ Y) :
    (acyclicStructure (nested W)).cof ((acyclicLift W).map f) ↔ W.cof f := Iff.rfl

end CategoryTheory.Waldhausen.Fibration.AllWeak
