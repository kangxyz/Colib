/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Functor.Rebase
public import Colib.CategoryTheory.Waldhausen.Additivity.DiagramIso
public import Colib.CategoryTheory.Waldhausen.Additivity.IntervalArrows

/-! # The actual pushout deformation normalized at the chosen zero arrow

Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedPushout.lean`
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

/-- The pushout at the identity of the chosen source zero is genuinely zero. -/
def pushoutZeroIso :
    (pushoutFunctor W a hc.app_cof).obj (Arrow.mk (𝟙 V.zero)) ≅ W.zero :=
  (pushoutFunctor_obj_isZero W a hc.app_cof V hF hG (Arrow.mk (𝟙 V.zero))
    V.isZero V.isZero).iso W.isZero

/-- Normalize only the distinguished zero arrow, by its unique actual zero iso. -/
def normalizedPushoutFunctor : Arrow C ⥤ D :=
  rebaseFunctor (pushoutFunctor W a hc.app_cof) (Arrow.mk (𝟙 V.zero)) W.zero
    (pushoutZeroIso V W a hF hG hc)

/-- The actual normalization is naturally isomorphic to the original pushout functor. -/
def normalizedPushoutIso : pushoutFunctor W a hc.app_cof ≅ normalizedPushoutFunctor V W a hF hG
    hc :=
  rebaseFunctorIso _ _ _ (pushoutZeroIso V W a hF hG hc)

@[simp] theorem normalizedPushoutFunctor_obj_zero :
    (normalizedPushoutFunctor V W a hF hG hc).obj (Arrow.mk (𝟙 V.zero)) = W.zero :=
  rebaseFunctor_obj_base _ _ _ _

/-- Normalization retains every actual two-degree S-diagram condition. -/
theorem normalizedPushoutFunctor_isSimplex₂ {n m : SimplexCategory} (A : Grid₂ n m ⥤ Arrow C)
    (hl : IsSimplex₂ V.cof V.weq (A ⋙ Arrow.leftFunc))
    (hr : IsSimplex₂ V.cof V.weq (A ⋙ Arrow.rightFunc)) :
    IsSimplex₂ W.cof W.weq (A ⋙ normalizedPushoutFunctor V W a hF hG hc) :=
  simplex₂_of_iso W (pushoutFunctor_isSimplex₂ V W a hF hG hc A hl hr)
    (Functor.isoWhiskerLeft A (normalizedPushoutIso V W a hF hG hc))

variable {n p m : SimplexCategory} (α β : n ⟶ p)
variable (h : ∀ i, α.toOrderHom i ≤ β.toOrderHom i)

/-- The chosen-zero normalized interval deformation. -/
def normalizedIntervalDiagram (A : Grid₂ p m ⥤ C) : Grid₂ n m ⥤ D :=
  intervalArrows α β h A ⋙ normalizedPushoutFunctor V W a hF hG hc

/-- The normalized interval deformation is still a genuine S-diagram. -/
theorem normalizedIntervalDiagram_isSimplex₂ {A : Grid₂ p m ⥤ C}
    (hA : IsSimplex₂ V.cof V.weq A) :
    IsSimplex₂ W.cof W.weq (normalizedIntervalDiagram V W a hF hG hc α β h A) :=
  normalizedPushoutFunctor_isSimplex₂ V W a hF hG hc _
    (hA.precomp V.cof V.weq α (𝟙 m)) (hA.precomp V.cof V.weq β (𝟙 m))

/-- Every comparison on a constant input grid is literally the identity arrow. -/
theorem intervalArrows_const (Z : C) :
    intervalArrows α β h ((Functor.const (Grid₂ p m)).obj Z) =
      (Functor.const (Grid₂ n m)).obj (Arrow.mk (𝟙 Z)) := rfl

/-- All mixed cuts and both endpoints now have exactly the chosen zero object
on every point of a constant-zero input grid. -/
theorem normalizedIntervalDiagram_zero_obj (x : Grid₂ n m) :
    (normalizedIntervalDiagram V W a hF hG hc α β h
      ((Functor.const (Grid₂ p m)).obj V.zero)).obj x = W.zero :=
  normalizedPushoutFunctor_obj_zero V W a hF hG hc

end CategoryTheory.Waldhausen.Additivity
