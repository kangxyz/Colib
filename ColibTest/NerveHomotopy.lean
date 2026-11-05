/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.NerveHomotopy

/-! Regression coverage for the genuine nerve cylinder, its orientation and
its exact based-vertex condition, with independent object/hom universes. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u v

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G : C ⥤ D} (α : F ⟶ G)

example : naturalTransformationCylinderFunctor α =
    Functor.uncurry.obj (ComposableArrows.mk₁ α) := rfl

example : (naturalTransformationNerveHomotopy α).h =
    naturalTransformationNerveCylinder α := rfl

example : SSet.ι₀ ≫ (naturalTransformationNerveHomotopy α).h = nerveMap F :=
  SSet.Homotopy.h₀ _

example : SSet.ι₁ ≫ (naturalTransformationNerveHomotopy α).h = nerveMap G :=
  SSet.Homotopy.h₁ _

example (c : C) :
    nerveVertexMap c ▷ Δ[1] ≫ naturalTransformationNerveCylinder α =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (α.app c)) :=
  naturalTransformationNerveCylinder_vertex α c

example (c : C) (h : F.obj c = G.obj c) (hα : α.app c = eqToHom h) :
    nerveVertexMap c ▷ Δ[1] ≫ naturalTransformationNerveCylinder α =
      CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫ nerveVertexMap (F.obj c) :=
  naturalTransformationNerveCylinder_based α c h hα
