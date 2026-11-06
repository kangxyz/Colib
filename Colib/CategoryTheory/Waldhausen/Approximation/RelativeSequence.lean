/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.SquareLift

/-!
# Relative lifting of whole source sequences

A natural transformation from the image of a source cofibration sequence to a
target sequence factors through the image of a new source cofibration sequence,
with a cofibration on every source component and a weak equivalence on every
target component. An arbitrary specified initial factorization is retained.
The proof iterates actual pushout square lifting, so both natural transformations
and the factorization equation are strict.

Implementation provenance: `Quillen/Waldhausen/Approximation/RelativeSequence.lean` at Quillen
commit
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
  {G : ℕ ⥤ C} {H : ℕ ⥤ D} (α : G ⋙ F ⟶ H)

/-- A stage in a relative lift of the specified natural transformation. -/
structure RelativeStage (n : ℕ) where
  /-- The source-category replacement object at stage `n`. -/
  obj : C
  /-- The cofibration from the original stage object `G.obj n` to its replacement. -/
  inclusion : G.obj n ⟶ obj
  /-- The weak comparison from the image of the replacement to `H.obj n`, factoring the original
  component `α.app n`. -/
  projection : F.obj obj ⟶ H.obj n
  cofibration : W.cof inclusion
  weak : V.weq projection
  factorization : F.map inclusion ≫ projection = α.app n

variable (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : ∀ {i j : ℕ} (f : i ⟶ j), W.cof (G.map f))

/-- The actual pushout-based step relative to the next original source vertex. -/
def relativeNextSquare {n : ℕ} (s : RelativeStage (W := W) (V := V) α n) :
    SquareLift (W := W) (V := V)
      (G.map (homOfLE (Nat.le_add_right n 1))) s.inclusion s.projection
      (H.map (homOfLE (Nat.le_add_right n 1))) (α.app (n + 1)) :=
  h.squareLift hF _ _ _ _ _ (hG _) s.cofibration (by
    rw [← Category.assoc, s.factorization]
    exact α.naturality _)

/-- The next factorization includes the next specified source object. -/
def relativeNext {n : ℕ} (s : RelativeStage (W := W) (V := V) α n) :
    RelativeStage (W := W) (V := V) α (n + 1) where
  obj := (relativeNextSquare α h hF hG s).obj
  inclusion := (relativeNextSquare α h hF hG s).fromSource
  projection := (relativeNextSquare α h hF hG s).projection
  cofibration := (relativeNextSquare α h hF hG s).fromSource_cof
  weak := (relativeNextSquare α h hF hG s).projection_weak
  factorization := (relativeNextSquare α h hF hG s).source_projection

/-- Recursive relative stages retain the given initial factorization exactly. -/
def relativeStage (s₀ : RelativeStage (W := W) (V := V) α 0) :
    (n : ℕ) → RelativeStage (W := W) (V := V) α n
  | 0 => s₀
  | n + 1 => relativeNext α h hF hG (relativeStage s₀ n)

variable (s₀ : RelativeStage (W := W) (V := V) α 0)

/-- The successive source maps are the actual relative pushout lifts. -/
def relativeStep (n : ℕ) :
    (relativeStage α h hF hG s₀ n).obj ⟶ (relativeStage α h hF hG s₀ (n + 1)).obj :=
  (relativeNextSquare α h hF hG (relativeStage α h hF hG s₀ n)).fromLift

/-- The whole relative replacement sequence in the source category. -/
def relativeSequence : ℕ ⥤ C :=
  Functor.ofSequence (relativeStep α h hF hG s₀)

/-- The source inclusion is a genuine natural transformation. -/
def relativeInclusion : G ⟶ relativeSequence α h hF hG s₀ :=
  NatTrans.ofSequence (fun n ↦ (relativeStage α h hF hG s₀ n).inclusion) (by
    intro n
    change G.map (homOfLE (Nat.le_add_right n 1)) ≫
      (relativeStage α h hF hG s₀ (n + 1)).inclusion =
      (relativeStage α h hF hG s₀ n).inclusion ≫
      (Functor.ofSequence (relativeStep α h hF hG s₀)).map
        (homOfLE (Nat.le_add_right n 1))
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (relativeNextSquare α h hF hG (relativeStage α h hF hG s₀ n)).square)

/-- The target comparison is also a genuine natural transformation after F. -/
def relativeProjection : relativeSequence α h hF hG s₀ ⋙ F ⟶ H :=
  NatTrans.ofSequence (fun n ↦ (relativeStage α h hF hG s₀ n).projection) (by
    intro n
    change F.map ((Functor.ofSequence (relativeStep α h hF hG s₀)).map _) ≫ _ = _
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (relativeNextSquare α h hF hG (relativeStage α h hF hG s₀ n)).lift_projection)

/-- Every original component maps by a cofibration into its replacement. -/
theorem relativeInclusion_cof (n : ℕ) :
    W.cof ((relativeInclusion α h hF hG s₀).app n) :=
  (relativeStage α h hF hG s₀ n).cofibration

/-- Every comparison component is the actual weak App2 projection. -/
theorem relativeProjection_weak (n : ℕ) :
    V.weq ((relativeProjection α h hF hG s₀).app n) :=
  (relativeStage α h hF hG s₀ n).weak

/-- The two transformations factor the original α, strictly and naturally. -/
theorem relative_factorization :
    Functor.whiskerRight (relativeInclusion α h hF hG s₀) F ≫
      relativeProjection α h hF hG s₀ = α := by
  ext n
  exact (relativeStage α h hF hG s₀ n).factorization

/-- Every arrow of the relative replacement sequence is a source cofibration. -/
theorem relativeSequence_map_cof {i j : ℕ} (f : i ⟶ j) :
    W.cof ((relativeSequence α h hF hG s₀).map f) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
  obtain rfl := Subsingleton.elim f (homOfLE (Nat.le_add_right i k))
  induction k with
  | zero => simpa using W.cof.id_mem ((relativeSequence α h hF hG s₀).obj i)
  | succ k ih =>
    have hf : homOfLE (Nat.le_add_right i (k + 1)) =
        homOfLE (Nat.le_add_right i k) ≫ homOfLE (Nat.le_add_right (i + k) 1) := rfl
    rw [hf, Functor.map_comp]
    apply W.cof.comp_mem _ _ ih
    change W.cof ((Functor.ofSequence (relativeStep α h hF hG s₀)).map _)
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (relativeNextSquare α h hF hG (relativeStage α h hF hG s₀ (i + k))).fromLift_cof

/-- The specified source starting vertex is unchanged. -/
@[simp]
theorem relativeSequence_obj_zero : (relativeSequence α h hF hG s₀).obj 0 = s₀.obj := rfl

/-- The specified initial source map is unchanged. -/
@[simp]
theorem relativeInclusion_app_zero : (relativeInclusion α h hF hG s₀).app 0 = s₀.inclusion := rfl

/-- The specified initial target map is unchanged. -/
@[simp]
theorem relativeProjection_app_zero : (relativeProjection α h hF hG s₀).app 0 = s₀.projection := rfl

/-- Pointwise weakness of the original transformation is reflected to the
source inclusion, so weak transformations factor through weak cofibrations. -/
theorem relativeInclusion_weak [V.weq.HasTwoOutOfThreeProperty]
    (hα : ∀ n, V.weq (α.app n)) (n : ℕ) :
    W.weq ((relativeInclusion α h hF hG s₀).app n) := by
  apply h.reflects
  apply V.weq.of_postcomp _ ((relativeProjection α h hF hG s₀).app n)
    (relativeProjection_weak α h hF hG s₀ n)
  change V.weq (F.map (relativeStage α h hF hG s₀ n).inclusion ≫
    (relativeStage α h hF hG s₀ n).projection)
  rw [(relativeStage α h hF hG s₀ n).factorization]
  exact hα n

end CategoryTheory.Waldhausen.HasApproximationProperty
