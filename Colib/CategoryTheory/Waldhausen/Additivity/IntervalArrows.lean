/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.PushoutPreservation
public import Colib.CategoryTheory.Waldhausen.Additivity.ZeroFactorization
public import Colib.CategoryTheory.Waldhausen.SConstruction.Bisimplicial

/-! # The genuine arrow-valued diagrams of the additivity deformation

Implementation provenance: `Quillen/Waldhausen/Additivity/IntervalArrows.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v'

namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (V : Structure C) (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

include hF hG in
/-- Pushout transport in independent interval and nerve degrees. -/
theorem pushoutFunctor_isSimplex₂ {n m : SimplexCategory} (A : Grid₂ n m ⥤ Arrow C)
    (hl : IsSimplex₂ V.cof V.weq (A ⋙ Arrow.leftFunc))
    (hr : IsSimplex₂ V.cof V.weq (A ⋙ Arrow.rightFunc)) :
    IsSimplex₂ W.cof W.weq (A ⋙ pushoutFunctor W a hc.app_cof) where
  zero t i := pushoutFunctor_obj_isZero W a hc.app_cof V hF hG _ (hl.zero t i) (hr.zero t i)
  cofibration t i j k hij hjk := pushoutFunctor_map_cof W a V hF hc _
    (hl.cofibration t i j k hij hjk) (hr.cofibration t i j k hij hjk)
  quotient t i j k hij hjk := pushoutFunctor_map_isPushout_of_exact W a hc.app_cof V hF hG
    _ _ _ _ (by simp only [← A.map_comp]; congr 1)
    (hl.cofibration t i j k hij hjk) (hr.cofibration t i j k hij hjk)
    (hl.quotient t i j k hij hjk) (hr.quotient t i j k hij hjk)
  weak s t i j hst hij := pushoutFunctor_map_weak_of_exact W a V hF hG hc _
    (hl.weak s t i j hst hij) (hr.weak s t i j hst hij)

variable {n p m : SimplexCategory}
variable (α β : n ⟶ p) (h : ∀ i, α.toOrderHom i ≤ β.toOrderHom i)

/-- Two pointwise ordered outer restrictions determine an actual arrow diagram. -/
def intervalArrows (A : Grid₂ p m ⥤ C) : Grid₂ n m ⥤ Arrow C where
  obj x := Arrow.mk (A.map (homOfLE (show (gridMap₂ α (𝟙 m)).obj x ≤
      (gridMap₂ β (𝟙 m)).obj x from ⟨le_rfl, h x.2.1.1, h x.2.1.2⟩)))
  map {x y} f := Arrow.homMk (A.map ((gridMap₂ α (𝟙 m)).map f))
    (A.map ((gridMap₂ β (𝟙 m)).map f))
      ((A.map_comp _ _).symm.trans ((congrArg A.map (Subsingleton.elim _ _)).trans (A.map_comp _
        _)))
  map_id _ := by apply Arrow.hom_ext <;> simp
  map_comp _ _ := by apply Arrow.hom_ext <;> simp

/-- The source diagram is exactly the first outer restriction. -/
theorem intervalArrows_left (A : Grid₂ p m ⥤ C) :
    intervalArrows α β h A ⋙ Arrow.leftFunc = gridMap₂ α (𝟙 m) ⋙ A := rfl

/-- The target diagram is exactly the second outer restriction. -/
theorem intervalArrows_right (A : Grid₂ p m ⥤ C) :
    intervalArrows α β h A ⋙ Arrow.rightFunc = gridMap₂ β (𝟙 m) ⋙ A := rfl

/-- The actual pushout deformation of a two-degree quotient diagram. -/
def deformedGrid (A : Grid₂ p m ⥤ C) : Grid₂ n m ⥤ D :=
  intervalArrows α β h A ⋙ pushoutFunctor W a hc.app_cof

include hF hG in
/-- The deformation retains every zero, cofibration, quotient pushout and weak map. -/
theorem deformedGrid_isSimplex₂ {A : Grid₂ p m ⥤ C} (hA : IsSimplex₂ V.cof V.weq A) :
    IsSimplex₂ W.cof W.weq (deformedGrid V W a hc α β h A) :=
  pushoutFunctor_isSimplex₂ V W a hF hG hc _
    (hA.precomp V.cof V.weq α (𝟙 m)) (hA.precomp V.cof V.weq β (𝟙 m))

/-- Independent inner restriction commutes with the actual arrow construction. -/
theorem intervalArrows_inner {m' : SimplexCategory} (ν : m' ⟶ m) (A : Grid₂ p m ⥤ C) :
    gridMap₂ (𝟙 n) ν ⋙ intervalArrows α β h A =
      intervalArrows α β h (gridMap₂ (𝟙 p) ν ⋙ A) := rfl

/-- Restricting the output interval degree is the actual composite restriction. -/
theorem intervalArrows_outer {n' : SimplexCategory} (μ : n' ⟶ n) (A : Grid₂ p m ⥤ C) :
    gridMap₂ μ (𝟙 m) ⋙ intervalArrows α β h A =
      intervalArrows (μ ≫ α) (μ ≫ β) (fun i ↦ h (μ.toOrderHom i)) A := rfl

/-- Restricting the input interval degree composes both index maps strictly. -/
theorem intervalArrows_input {p' : SimplexCategory} (γ : p ⟶ p') (A : Grid₂ p' m ⥤ C) :
    intervalArrows α β h (gridMap₂ γ (𝟙 m) ⋙ A) =
      intervalArrows (α ≫ γ) (β ≫ γ) (fun i ↦ γ.toOrderHom.monotone (h i)) A := rfl

end CategoryTheory.Waldhausen.Additivity
