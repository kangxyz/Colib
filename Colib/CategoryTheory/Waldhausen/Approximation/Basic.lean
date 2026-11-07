/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Waldhausen approximation properties

App1 reflects weak equivalences. The cofibration version of App2 factors maps out of an image
    through an image cofibration and a weak equivalence. Exactness and cylinder hypotheses are
    separate conditions.

Implementation provenance: `Quillen/Waldhausen/Approximation/Basic.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe v u v' u'

namespace CategoryTheory.Waldhausen

/-- Waldhausen's App1 and App2, using the cofibration version of App2.
Exactness of the functor and the cylinder hypotheses are separate. -/
structure HasApproximationProperty {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (W : Structure C) (W' : Structure D)
    (F : C ⥤ D) : Prop where
  reflects {X Y : C} (f : X ⟶ Y) : W'.weq (F.map f) → W.weq f
  lift {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    ∃ (X' : C) (i : X ⟶ X') (p : F.obj X' ⟶ Y),
      W.cof i ∧ W'.weq p ∧ F.map i ≫ p = f

end CategoryTheory.Waldhausen

end
