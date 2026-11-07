/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.Basic
public import Colib.CategoryTheory.Waldhausen.Approximation.FiniteReplacement
public import Colib.KTheory.Waldhausen.Map
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.CategoryTheory.Waldhausen.ExactFunctor

/-!
# Relative sequence lifting across approximation functors

App2 constructs an actual cofibration sequence in the source of an arbitrary
functor, together with a strictly natural, pointwise weak comparison to a
specified target sequence. The initial source object and comparison are retained.
Restriction gives a replacement of any finite flag across the original functor.
The choices are not asserted to be functorial in the input diagram.

These are diagram-lifting lemmas, not the approximation theorem. In particular,
nonempty categories of replacements do not assert their contractibility.

Implementation provenance: `Quillen/Waldhausen/Approximation/SequenceLift.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.FunctorialFactorization



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory.Waldhausen.HasApproximationProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}

/-- A chosen App2 factorization retains the actual source and target maps. -/
structure Step {X : C} {Y : D} (f : F.obj X ⟶ Y) where
  /-- The source-category middle object in the App2 factorization of `f`. -/
  obj : C
  /-- The cofibration from the original source `X` into the middle object. -/
  inclusion : X ⟶ obj
  /-- The weak equivalence from the image of the middle object to `Y`, whose composite with the
  image of `inclusion` is `f`. -/
  projection : F.obj obj ⟶ Y
  cofibration : W.cof inclusion
  weak : V.weq projection
  factorization : F.map inclusion ≫ projection = f

/-- App2 supplies a factorization for every actual arrow out of the image. -/
def chooseStep (h : HasApproximationProperty W V F)
    {X : C} {Y : D} (f : F.obj X ⟶ Y) : Step (W := W) (V := V) f :=
  Classical.choice (by
    obtain ⟨X', i, p, hi, hp, fac⟩ := h.lift f
    exact ⟨⟨X', i, p, hi, hp, fac⟩⟩)

/-- The successive source objects and their maps to the given target sequence. -/
def sequenceStage (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) : (n : ℕ) → Σ X' : C, F.obj X' ⟶ G.obj n
  | 0 => ⟨X, p⟩
  | n + 1 =>
    let s := h.chooseStep ((sequenceStage h G p n).2 ≫
      G.map (homOfLE (Nat.le_add_right n 1)))
    ⟨s.obj, s.projection⟩

/-- Each successive source map is the cofibration given by App2. -/
def sequenceStep (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) (n : ℕ) :
    (h.sequenceStage G p n).1 ⟶ (h.sequenceStage G p (n + 1)).1 :=
  (h.chooseStep ((h.sequenceStage G p n).2 ≫
    G.map (homOfLE (Nat.le_add_right n 1)))).inclusion

/-- A sequence of genuine source objects and cofibrations lifting the target. -/
def sequenceLift (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) : ℕ ⥤ C :=
  Functor.ofSequence (h.sequenceStep G p)

/-- The replacement comparison is a strictly natural transformation after the
original functor, not merely a collection of weak equivalences. -/
def sequenceComparison (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) : h.sequenceLift G p ⋙ F ⟶ G :=
  NatTrans.ofSequence (fun n ↦ (h.sequenceStage G p n).2) (by
    intro n
    change F.map ((Functor.ofSequence (h.sequenceStep G p)).map _) ≫ _ = _
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (h.chooseStep ((h.sequenceStage G p n).2 ≫
      G.map (homOfLE (Nat.le_add_right n 1)))).factorization)

@[simp]
theorem sequenceLift_obj_zero (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) : (h.sequenceLift G p).obj 0 = X := rfl

@[simp]
theorem sequenceComparison_app_zero (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) : (h.sequenceComparison G p).app 0 = p := rfl

/-- Every source arrow in the lifted sequence is a cofibration. -/
theorem sequenceLift_map_cof (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) {i j : ℕ} (f : i ⟶ j) :
    W.cof ((h.sequenceLift G p).map f) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
  obtain rfl := Subsingleton.elim f (homOfLE (Nat.le_add_right i k))
  induction k with
  | zero => simpa using W.cof.id_mem ((h.sequenceLift G p).obj i)
  | succ k ih =>
    have hf : homOfLE (Nat.le_add_right i (k + 1)) =
        homOfLE (Nat.le_add_right i k) ≫ homOfLE (Nat.le_add_right (i + k) 1) := rfl
    rw [hf, Functor.map_comp]
    apply W.cof.comp_mem _ _ ih
    rw [sequenceLift, Functor.ofSequence_map_homOfLE_succ]
    exact (h.chooseStep ((h.sequenceStage G p (i + k)).2 ≫
      G.map (homOfLE (Nat.le_add_right (i + k) 1)))).cofibration

/-- A weak initial comparison gives a pointwise weak comparison on the whole
sequence. No saturation or cylinder assumption is needed for this construction. -/
theorem sequenceComparison_weak (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) (hp : V.weq p) (n : ℕ) :
    V.weq ((h.sequenceComparison G p).app n) := by
  cases n with
  | zero => exact hp
  | succ n => exact (h.chooseStep ((h.sequenceStage G p n).2 ≫
      G.map (homOfLE (Nat.le_add_right n 1)))).weak

/-- App1 and target saturation reflect weakness through an actual comparison
square. This applies to any diagrams, not only the chosen replacements. -/
theorem weak_of_comparison [V.weq.HasTwoOutOfThreeProperty]
    (h : HasApproximationProperty W V F)
    {X X' : C} {Y Y' : D} (a : X ⟶ X') (b : Y ⟶ Y')
    (p : F.obj X ⟶ Y) (p' : F.obj X' ⟶ Y')
    (comm : F.map a ≫ p' = p ≫ b)
    (hp : V.weq p) (hp' : V.weq p') (hb : V.weq b) : W.weq a := by
  apply h.reflects
  apply V.weq.of_postcomp _ p' hp'
  rw [comm]
  exact V.weq.comp_mem _ _ hp hb

/-- A weak target arrow lifts to a genuine weak cofibration in the source. -/
theorem sequenceLift_map_weak [V.weq.HasTwoOutOfThreeProperty]
    (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) (hp : V.weq p)
    {i j : ℕ} (f : i ⟶ j) (hf : V.weq (G.map f)) :
    W.weq ((h.sequenceLift G p).map f) :=
  h.weak_of_comparison _ _ _ _ ((h.sequenceComparison G p).naturality f)
    (h.sequenceComparison_weak G p hp i) (h.sequenceComparison_weak G p hp j) hf

open FunctorialFactorization

/-- The relative lift of a finite diagram, obtained by constant extension and
restriction. Its vertices live in the source category of the original functor. -/
def finiteLift (h : HasApproximationProperty W V F) (n : ℕ)
    (G : ComposableArrows D n) {X : C} (p : F.obj X ⟶ G.obj 0) :
    ComposableArrows C n :=
  finiteIndex n ⋙ h.sequenceLift ((extendFinite n).obj G) p

/-- The genuine natural comparison from the image of the finite lift. -/
def finiteComparison (h : HasApproximationProperty W V F) (n : ℕ)
    (G : ComposableArrows D n) {X : C} (p : F.obj X ⟶ G.obj 0) :
    h.finiteLift n G p ⋙ F ⟶ G :=
  Functor.whiskerLeft (finiteIndex n) (h.sequenceComparison ((extendFinite n).obj G) p) ≫
    (finiteRoundTripIso n).hom.app G

/-- The initial source vertex is unchanged by finite lifting. -/
@[simp]
theorem finiteLift_obj_zero (h : HasApproximationProperty W V F) (n : ℕ)
    (G : ComposableArrows D n) {X : C} (p : F.obj X ⟶ G.obj 0) :
    (h.finiteLift n G p).obj 0 = X := rfl

/-- The initial comparison is the specified original arrow. -/
@[simp]
theorem finiteComparison_app_zero (h : HasApproximationProperty W V F) (n : ℕ)
    (G : ComposableArrows D n) {X : C} (p : F.obj X ⟶ G.obj 0) :
    (h.finiteComparison n G p).app 0 = p := by
  change p ≫ G.map _ = p
  have he : (finiteClampIso n).hom.app (0 : Fin (n + 1)) = 𝟙 (0 : Fin (n + 1)) :=
    Subsingleton.elim _ _
  rw [he, G.map_id, Category.comp_id]

/-- Every arrow of the finite lift is a genuine source cofibration. -/
theorem finiteLift_map_cof (h : HasApproximationProperty W V F) (n : ℕ)
    (G : ComposableArrows D n) {X : C} (p : F.obj X ⟶ G.obj 0)
    {i j : Fin (n + 1)} (f : i ⟶ j) : W.cof ((h.finiteLift n G p).map f) :=
  h.sequenceLift_map_cof ((extendFinite n).obj G) p ((finiteIndex n).map f)

/-- The finite comparison is pointwise weak when its initial value is weak. -/
theorem finiteComparison_weak (h : HasApproximationProperty W V F) (n : ℕ)
    (G : ComposableArrows D n) {X : C} (p : F.obj X ⟶ G.obj 0)
    (hp : V.weq p) (i : Fin (n + 1)) : V.weq ((h.finiteComparison n G p).app i) := by
  apply V.weq.comp_mem
  · exact h.sequenceComparison_weak ((extendFinite n).obj G) p hp i.val
  · exact V.weq_iso _ inferInstance

/-- Finite lifting also reflects weak target arrows, by App1 and saturation. -/
theorem finiteLift_map_weak [V.weq.HasTwoOutOfThreeProperty]
    (h : HasApproximationProperty W V F) (n : ℕ)
    (G : ComposableArrows D n) {X : C} (p : F.obj X ⟶ G.obj 0) (hp : V.weq p)
    {i j : Fin (n + 1)} (f : i ⟶ j) (hf : V.weq (G.map f)) :
    W.weq ((h.finiteLift n G p).map f) :=
  h.weak_of_comparison _ _ _ _ ((h.finiteComparison n G p).naturality f)
    (h.finiteComparison_weak n G p hp i) (h.finiteComparison_weak n G p hp j) hf

end CategoryTheory.Waldhausen.HasApproximationProperty
