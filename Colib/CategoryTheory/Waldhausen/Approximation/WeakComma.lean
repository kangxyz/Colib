/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.SquareLift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.IsConnected

/-!
# Genuine weak comma categories for approximation functors

Exactness gives the original functor between categories of weak equivalences.
App2 makes every costructured-arrow category nonempty. App1, target saturation,
and the relative pushout square lift give a common successor for every pair of
objects, by actual weak cofibrations in the source. Hence these comma categories
are connected. Connectedness is strictly weaker than the contractibility needed
by the available Quillen Theorem A, and no contractibility is asserted here.

Implementation provenance: `Quillen/Waldhausen/Approximation/WeakComma.lean` at Quillen commit
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

/-- The original exact functor on actual weak-equivalence subcategories. -/
def IsExact.weakFunctor (hF : IsExact W.cof W.weq V.cof V.weq F) :
    WideSubcategory W.weq ⥤ WideSubcategory V.weq where
  obj X := ⟨F.obj X.obj⟩
  map f := ⟨F.map f.hom, hF.weak _ f.property⟩
  map_id X := by apply WideSubcategory.hom_ext; exact F.map_id _
  map_comp f g := by apply WideSubcategory.hom_ext; exact F.map_comp _ _

namespace HasApproximationProperty

variable (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (Y : WideSubcategory V.weq)

/-- The original weak-map comma category, with no replacement of its objects. -/
abbrev WeakComma := CostructuredArrow hF.weakFunctor Y

/-- App2 applied at the source zero gives an actual comma object. -/
def weakCommaPoint : WeakComma hF Y :=
  let s := h.chooseStep ((hF.zero W.isZero).to_ Y.obj)
  CostructuredArrow.mk (Y := (⟨s.obj⟩ : WideSubcategory W.weq)) ⟨s.projection, s.weak⟩

include h in
/-- Every genuine weak-map comma category is nonempty. -/
theorem weakComma_nonempty : Nonempty (WeakComma hF Y) := ⟨weakCommaPoint h hF Y⟩

variable [V.weq.HasTwoOutOfThreeProperty]

/-- Two original weak arrows into Y admit a common target in the source,
with strictly commuting weak-cofibration comparison maps. -/
def weakCommaPairSquare (A B : WeakComma hF Y) :
    SquareLift (W := W) (V := V)
      (W.isZero.to_ A.left.obj) (W.isZero.to_ B.left.obj)
      B.hom.hom (𝟙 Y.obj) A.hom.hom :=
  h.squareLift hF _ _ _ _ _ (W.cof_zero _) (W.cof_zero _)
    ((hF.zero W.isZero).eq_of_src _ _)

/-- The common successor is an actual object of the original comma category. -/
def weakCommaPairTarget (A B : WeakComma hF Y) : WeakComma hF Y :=
  let s := weakCommaPairSquare h hF Y A B
  CostructuredArrow.mk (Y := (⟨s.obj⟩ : WideSubcategory W.weq))
    ⟨s.projection, s.projection_weak⟩

/-- First comparison in the actual comma category. -/
def weakCommaPairLeft (A B : WeakComma hF Y) : A ⟶ weakCommaPairTarget h hF Y A B :=
  let s := weakCommaPairSquare h hF Y A B
  CostructuredArrow.homMk
    (⟨s.fromSource, s.fromSource_weak h A.hom.property⟩ : A.left ⟶ ⟨s.obj⟩)
    (by apply WideSubcategory.hom_ext; exact s.source_projection)

/-- Second comparison in the actual comma category. -/
def weakCommaPairRight (A B : WeakComma hF Y) : B ⟶ weakCommaPairTarget h hF Y A B :=
  let s := weakCommaPairSquare h hF Y A B
  CostructuredArrow.homMk
    (⟨s.fromLift, s.fromLift_weak h B.hom.property (V.weq.id_mem _)⟩ : B.left ⟶ ⟨s.obj⟩)
    (by
      apply WideSubcategory.hom_ext
      change F.map s.fromLift ≫ s.projection = B.hom.hom
      simpa only [Category.comp_id] using s.lift_projection)

/-- Both comparison arrows are genuine source cofibrations as well as weak. -/
theorem weakCommaPairLeft_cof (A B : WeakComma hF Y) :
    W.cof (weakCommaPairLeft h hF Y A B).left.hom :=
  (weakCommaPairSquare h hF Y A B).fromSource_cof

/-- Both comparison arrows are genuine source cofibrations as well as weak. -/
theorem weakCommaPairRight_cof (A B : WeakComma hF Y) :
    W.cof (weakCommaPairRight h hF Y A B).left.hom :=
  (weakCommaPairSquare h hF Y A B).fromLift_cof

include h in
/-- Common successors prove connectedness of the original weak comma category.
No statement about higher homotopy groups or contractibility is hidden here. -/
theorem weakComma_connected : IsConnected (WeakComma hF Y) := by
  let := weakComma_nonempty h hF Y
  apply zigzag_isConnected
  intro A B
  exact Zigzag.of_hom_inv (weakCommaPairLeft h hF Y A B) (weakCommaPairRight h hF Y A B)

end HasApproximationProperty

end CategoryTheory.Waldhausen
