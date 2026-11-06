/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.SequenceLift

/-!
# Relative square lifting across an approximation functor

An exact functor satisfying App2 lifts a commutative target square relative to
two source cofibrations. The proof takes their actual pushout in the source,
uses exactness to descend the target maps, and applies App2 once. It produces
a strictly commuting source square, a weak projection, and cofibrations on
both new sides. With target saturation, App1 proves the corresponding weak
source arrows when the target arrows are weak.

This is the basic relative inductive step for finite-diagram approximation.
No lifting, contractibility, or K-equivalence endpoint is assumed.

Implementation provenance: `Quillen/Waldhausen/Approximation/SquareLift.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory.Waldhausen.HasApproximationProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}

/-- A relative square replacement retains all original maps and strict
commutativity, with cofibrations along both new sides. -/
structure SquareLift {A B A' : C} {Y Z : D}
    (a : A ⟶ B) (i : A ⟶ A') (p : F.obj A' ⟶ Y)
    (b : Y ⟶ Z) (q : F.obj B ⟶ Z) where
  /-- The source-category object completing the relative square replacement. -/
  obj : C
  /-- The cofibration from `B` into the square replacement, lifting the target map `q`. -/
  fromSource : B ⟶ obj
  /-- The cofibration from the previously lifted object `A'` into the replacement, compatible
  with `a` and `i` by `square`. -/
  fromLift : A' ⟶ obj
  /-- The weak comparison from the image of the square replacement to `Z`, compatible with both
  specified target maps. -/
  projection : F.obj obj ⟶ Z
  fromSource_cof : W.cof fromSource
  fromLift_cof : W.cof fromLift
  projection_weak : V.weq projection
  square : a ≫ fromSource = i ≫ fromLift
  source_projection : F.map fromSource ≫ projection = q
  lift_projection : F.map fromLift ≫ projection = p ≫ b

/-- Actual pushout descent and App2 give the relative square replacement. -/
def squareLift (h : HasApproximationProperty W V F)
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    {A B A' : C} {Y Z : D} (a : A ⟶ B) (i : A ⟶ A')
    (p : F.obj A' ⟶ Y) (b : Y ⟶ Z) (q : F.obj B ⟶ Z)
    (ha : W.cof a) (hi : W.cof i)
    (comm : F.map a ≫ q = F.map i ≫ p ≫ b) :
    SquareLift (W := W) (V := V) a i p b q :=
  Classical.choice (by
    obtain ⟨P, g, j, hP⟩ := W.pushout_exists a i ha
    let hFP := hF.pushout ha hP
    let r : F.obj P ⟶ Z := hFP.desc q (p ≫ b) comm
    obtain ⟨Q, k, t, hk, ht, hkt⟩ := h.lift r
    refine ⟨⟨Q, g ≫ k, j ≫ k, t,
      W.cof.comp_mem _ _ (W.cof_pushout hi hP.flip) hk,
      W.cof.comp_mem _ _ (W.cof_pushout ha hP) hk, ht, ?_, ?_, ?_⟩⟩
    · simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ k) hP.w
    · rw [F.map_comp, Category.assoc, hkt]
      exact hFP.inl_desc q (p ≫ b) comm
    · rw [F.map_comp, Category.assoc, hkt]
      exact hFP.inr_desc q (p ≫ b) comm)

namespace SquareLift

variable [V.weq.HasTwoOutOfThreeProperty]
  (h : HasApproximationProperty W V F)
  {A B A' : C} {Y Z : D} {a : A ⟶ B} {i : A ⟶ A'}
  {p : F.obj A' ⟶ Y} {b : Y ⟶ Z} {q : F.obj B ⟶ Z}
  (L : SquareLift (W := W) (V := V) a i p b q)

include h in
/-- The lifted relative side is weak when the target side and old comparison
are weak. Together with its structural field this is a weak cofibration. -/
theorem fromLift_weak (hp : V.weq p) (hb : V.weq b) : W.weq L.fromLift :=
  h.weak_of_comparison _ _ _ _ L.lift_projection hp L.projection_weak hb

include h in
/-- A weak specified source comparison makes the new source side weak. -/
theorem fromSource_weak (hq : V.weq q) : W.weq L.fromSource := by
  apply h.reflects
  apply V.weq.of_postcomp _ L.projection L.projection_weak
  rw [L.source_projection]
  exact hq

end SquareLift

/-- TT's arrow factorization condition, without the cofibration requirement,
implies App2 using genuine source cofibration/weak factorizations. This is the
construction in TT, proof of 1.9.1; no comparison conclusion is used. -/
theorem of_factorization (T : FunctorialFactorization W)
    (hweak : ∀ {X Y : C} (f : X ⟶ Y), W.weq f → V.weq (F.map f))
    (hreflect : ∀ {X Y : C} (f : X ⟶ Y), V.weq (F.map f) → W.weq f)
    (hlift : ∀ {X : C} {Y : D} (f : F.obj X ⟶ Y),
      ∃ (X' : C) (a : X ⟶ X') (p : F.obj X' ⟶ Y), V.weq p ∧ F.map a ≫ p = f) :
    HasApproximationProperty W V F where
  reflects := hreflect
  lift f := by
    obtain ⟨X', a, p, hp, fac⟩ := hlift f
    let t := Arrow.mk a
    refine ⟨T.middle.obj t, T.inclusion.app t, F.map (T.projection.app t) ≫ p,
      T.cofibration t, V.weq.comp_mem _ _ (hweak _ (T.weak t)) hp, ?_⟩
    rw [← Category.assoc, ← F.map_comp, T.factorization]
    exact fac

/-- A full, essentially surjective functor that preserves and reflects weak
arrows satisfies App2 when the source has actual cofibration factorizations.
Fullness lifts a strict arrow after an actual target isomorphism; no derived
fullness or strictification principle is silently substituted for it. -/
theorem of_full_essSurj [F.Full] [F.EssSurj] (T : FunctorialFactorization W)
    (hweak : ∀ {X Y : C} (f : X ⟶ Y), W.weq f → V.weq (F.map f))
    (hreflect : ∀ {X Y : C} (f : X ⟶ Y), V.weq (F.map f) → W.weq f) :
    HasApproximationProperty W V F :=
  of_factorization T hweak hreflect (by
    intro X Y f
    refine ⟨F.objPreimage Y, F.preimage (f ≫ (F.objObjPreimageIso Y).inv),
      (F.objObjPreimageIso Y).hom, V.weq_iso _ inferInstance, ?_⟩
    simp)

end CategoryTheory.Waldhausen.HasApproximationProperty
