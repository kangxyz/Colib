/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.Basic
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ReflexiveFactorization
public import Colib.KTheory.Waldhausen.AsSmall.Acyclic
public import Colib.CategoryTheory.Waldhausen.AsSmall.Joint
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceCancellation

/-! # Actual approximation transport through the existing small model

App1/App2 is transported by the actual up/down functors, retaining the
original factors. The existing joint-cylinder transport specializes to the
reflexive weak pair. Original S-map naturality carries complete weakness
back through the genuine realization homeomorphisms.

Implementation provenance:
`Quillen/Waldhausen/SmallModel/Approximation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat SSet
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}

/-- App1 and App2 are transported through the original actual small-model
functor; each lifted factor is the actual up-map of a base App2 factor. -/
theorem HasApproximationProperty.asSmall (h : HasApproximationProperty W V F) :
    HasApproximationProperty W.asSmall V.asSmall (asSmallFunctor F) where
  reflects f hf := h.reflects (AsSmall.down.map f) hf
  lift f := by
    obtain ⟨X', i, p, hi, hp, he⟩ := h.lift (AsSmall.down.map f)
    exact ⟨(AsSmall.up : C ⥤ AsSmall.{0} C).obj X',
      (AsSmall.up : C ⥤ AsSmall.{0} C).map i, (AsSmall.up : D ⥤ AsSmall.{0} D).map p, hi, hp,
      congrArg (AsSmall.up : D ⥤ AsSmall.{0} D).map he⟩

/-- The transported reflexive pair is the literal reflexive small-model pair. -/
@[simp] theorem Fibration.NestedWeakEquivalences.refl_asSmall :
    (Fibration.NestedWeakEquivalences.refl W).asSmall =
      Fibration.NestedWeakEquivalences.refl W.asSmall := rfl

/-- The existing genuine joint transport applies to the exact original weak class. -/
def Fibration.RowFactorization.JointData.reflexiveAsSmall
    (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W)) :
    Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W.asSmall) :=
  J.asSmall

/-- Complete weakness of the actual small-model S-map implies complete weakness
of the unchanged original S-map by its strictly natural homeomorphism square. -/
theorem deloopingMap_isWeakHomotopyEquivalence_of_asSmall
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (h : IsWeakHomotopyEquivalence (deloopingMap hF.asSmall).hom) :
    IsWeakHomotopyEquivalence (deloopingMap hF).hom := by
  have hc := h.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    W.asSmallDeloopingHomeomorph.toHomotopyEquiv)
  rw [← asSmallDeloopingHomeomorph_naturality] at hc
  exact hc.of_comp_right
    (isWeakHomotopyEquivalence_of_homotopyEquiv V.asSmallDeloopingHomeomorph.toHomotopyEquiv)

end CategoryTheory.Waldhausen
