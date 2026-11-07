/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.SequenceLift
public import Colib.CategoryTheory.Waldhausen.Approximation.WeakFlags
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Actual weak-flag replacement objects for approximation functors

Postcomposition by an exact functor acts on the existing weak-equivalence flag
categories. App2 constructs a source flag and an actual weak natural comparison
to any target flag. The source flag starts at the specified source zero object;
its comparison at zero is exactly the unique isomorphism between zero objects.
Consequently the original weak-flag comma category is nonempty in every degree.
This is not a contractibility statement or a K-theory comparison theorem.

Implementation provenance: `Quillen/Waldhausen/Approximation/FlagLift.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}

/-- The genuine weak-flag functor associated to the original exact functor. -/
def IsExact.weakFlagFunctor (hF : IsExact W.cof W.weq V.cof V.weq F) (n : ℕ) :
    WeakFlag W.cof W.weq n ⥤ WeakFlag V.cof V.weq n where
  obj A := {
    diagram := A.diagram ⋙ F
    zero := hF.zero A.zero
    cofibration f := hF.cofibration _ (A.cofibration f) }
  map α := ⟨Functor.whiskerRight α.val F, fun i ↦ hF.weak _ (α.property i)⟩
  map_id A := by apply Subtype.ext; ext i; exact F.map_id _
  map_comp α β := by apply Subtype.ext; ext i; exact F.map_comp _ _

namespace HasApproximationProperty

variable (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F) (n : ℕ)

/-- The chosen starting arrow is the actual zero-object isomorphism. -/
def flagZeroComparison (G : WeakFlag V.cof V.weq n) : F.obj W.zero ⟶ G.diagram.obj 0 :=
  ((hF.zero W.isZero).iso G.zero).hom

/-- A genuine source flag whose image is pointwise weakly equivalent to the
specified target flag. This choice is not asserted to be functorial in flags. -/
def flagLift (G : WeakFlag V.cof V.weq n) : WeakFlag W.cof W.weq n where
  diagram := h.finiteLift n G.diagram (flagZeroComparison hF n G)
  zero := W.isZero
  cofibration f := h.finiteLift_map_cof n G.diagram _ f

/-- The comparison is a morphism of the original weak-flag category. -/
def flagComparison (G : WeakFlag V.cof V.weq n) :
    (hF.weakFlagFunctor n).obj (h.flagLift hF n G) ⟶ G :=
  ⟨h.finiteComparison n G.diagram (flagZeroComparison hF n G),
    h.finiteComparison_weak n G.diagram (flagZeroComparison hF n G)
      (by
        change V.weq (((hF.zero W.isZero).iso G.zero).hom)
        exact V.weq_iso _ inferInstance)⟩

/-- The replacement starts at the chosen zero without rebasing the source. -/
@[simp]
theorem flagLift_obj_zero (G : WeakFlag V.cof V.weq n) :
    (h.flagLift hF n G).diagram.obj 0 = W.zero := rfl

/-- The comparison at zero is the original canonical zero isomorphism. -/
@[simp]
theorem flagComparison_app_zero (G : WeakFlag V.cof V.weq n) :
    (h.flagComparison hF n G).val.app 0 = ((hF.zero W.isZero).iso G.zero).hom :=
  h.finiteComparison_app_zero n G.diagram _

/-- An actual object of the weak-map comma category over the given target flag. -/
def flagCommaPoint (G : WeakFlag V.cof V.weq n) :
    CostructuredArrow (hF.weakFlagFunctor n) G :=
  CostructuredArrow.mk (h.flagComparison hF n G)

include h in
/-- Every target flag has a replacement in the source of the original functor. -/
theorem flagComma_nonempty (G : WeakFlag V.cof V.weq n) :
    Nonempty (CostructuredArrow (hF.weakFlagFunctor n) G) :=
  ⟨h.flagCommaPoint hF n G⟩

include h in
/-- A useful existential form retaining the actual functor and chosen zero. -/
theorem exists_weakFlag_comparison (G : WeakFlag V.cof V.weq n) :
    ∃ A : WeakFlag W.cof W.weq n,
      A.diagram.obj 0 = W.zero ∧ Nonempty ((hF.weakFlagFunctor n).obj A ⟶ G) :=
  ⟨h.flagLift hF n G, rfl, ⟨h.flagComparison hF n G⟩⟩

end HasApproximationProperty

end CategoryTheory.Waldhausen
