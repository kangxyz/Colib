/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.RelativeSequence
public import Colib.CategoryTheory.Waldhausen.Approximation.FlagLift

/-!
# App2 factorization for genuine finite flags

Every actual natural transformation from the image of a source cofibration flag
to a target cofibration flag factors through a source cofibration flag. The first
leg is pointwise a cofibration and the second leg is pointwise a weak equivalence.
This is proved by relative pushout induction, not by assuming diagram lifting.
The initial source object is retained. If the original transformation was weak,
the source leg is pointwise weak by App1 and target saturation.

Implementation provenance: `Quillen/Waldhausen/Approximation/RelativeFlags.lean` at Quillen commit
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

open FunctorialFactorization

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F) {n : ℕ}
  (A : WeakFlag W.cof W.weq n) (B : WeakFlag V.cof V.weq n)
  (α : A.diagram ⋙ F ⟶ B.diagram)

/-- Constant extension of the original comparison beyond its final vertex. -/
def extendedFlagComparison : (extendFinite n).obj A.diagram ⋙ F ⟶
    (extendFinite n).obj B.diagram :=
  Functor.whiskerLeft (clampIndex n) α

/-- The initial stage uses the original source zero, its identity inclusion,
and the original comparison, which is an isomorphism between zero objects. -/
def flagInitialStage : RelativeStage (W := W) (V := V) (extendedFlagComparison A B α) 0 where
  obj := A.diagram.obj 0
  inclusion := 𝟙 _
  projection := α.app 0
  cofibration := W.cof.id_mem _
  weak := V.weq_iso _ ((hF.zero A.zero).isIso B.zero _)
  factorization := by
    simp only [F.map_id, Category.id_comp]
    rfl

/-- The relative source sequence after constant extension. -/
def flagRelativeSequence : ℕ ⥤ C :=
  relativeSequence (extendedFlagComparison A B α) h hF
    (fun f ↦ A.cofibration ((clampIndex n).map f)) (flagInitialStage hF A B α)

/-- The new genuine source flag. -/
def relativeFlag : WeakFlag W.cof W.weq n where
  diagram := finiteIndex n ⋙ flagRelativeSequence h hF A B α
  zero := A.zero
  cofibration f := relativeSequence_map_cof (extendedFlagComparison A B α) h hF
    (fun f ↦ A.cofibration ((clampIndex n).map f)) (flagInitialStage hF A B α)
    ((finiteIndex n).map f)

/-- The inclusion of the whole original source flag into its relative lift. -/
def relativeFlagInclusion : A.diagram ⟶ (relativeFlag h hF A B α).diagram :=
  (finiteRoundTripIso n).inv.app A.diagram ≫
    Functor.whiskerLeft (finiteIndex n)
      (relativeInclusion (extendedFlagComparison A B α) h hF
        (fun f ↦ A.cofibration ((clampIndex n).map f)) (flagInitialStage hF A B α))

/-- The comparison to the entire original target flag. -/
def relativeFlagProjection : (relativeFlag h hF A B α).diagram ⋙ F ⟶ B.diagram :=
  Functor.whiskerLeft (finiteIndex n)
    (relativeProjection (extendedFlagComparison A B α) h hF
      (fun f ↦ A.cofibration ((clampIndex n).map f)) (flagInitialStage hF A B α)) ≫
    (finiteRoundTripIso n).hom.app B.diagram

/-- Pointwise cofibrancy of the original source inclusion. -/
theorem relativeFlagInclusion_cof (i : Fin (n + 1)) :
    W.cof ((relativeFlagInclusion h hF A B α).app i) := by
  apply W.cof.comp_mem
  · exact W.cof_iso _ inferInstance
  · exact relativeInclusion_cof (extendedFlagComparison A B α) h hF
      (fun f ↦ A.cofibration ((clampIndex n).map f)) (flagInitialStage hF A B α) i.val

/-- Pointwise weakness of the original target comparison. -/
theorem relativeFlagProjection_weak (i : Fin (n + 1)) :
    V.weq ((relativeFlagProjection h hF A B α).app i) := by
  apply V.weq.comp_mem
  · exact relativeProjection_weak (extendedFlagComparison A B α) h hF
      (fun f ↦ A.cofibration ((clampIndex n).map f)) (flagInitialStage hF A B α) i.val
  · exact V.weq_iso _ inferInstance

/-- The constructed natural transformations factor the original map of flags. -/
theorem relativeFlag_factorization :
    Functor.whiskerRight (relativeFlagInclusion h hF A B α) F ≫
      relativeFlagProjection h hF A B α = α := by
  ext i
  let s := relativeStage (extendedFlagComparison A B α) h hF
    (fun f ↦ A.cofibration ((clampIndex n).map f)) (flagInitialStage hF A B α) i.val
  change F.map (((finiteRoundTripIso n).inv.app A.diagram).app i ≫ s.inclusion) ≫
    (s.projection ≫ ((finiteRoundTripIso n).hom.app B.diagram).app i) = α.app i
  rw [F.map_comp, Category.assoc, ← Category.assoc (F.map s.inclusion), s.factorization]
  have hn := congrArg (fun η ↦ η.app i) ((finiteRoundTripIso n).hom.naturality α)
  change (extendedFlagComparison A B α).app i.val ≫
    ((finiteRoundTripIso n).hom.app B.diagram).app i =
    F.map (((finiteRoundTripIso n).hom.app A.diagram).app i) ≫ α.app i at hn
  rw [hn, ← Category.assoc, ← F.map_comp]
  simp

/-- Relative flag lifting retains the original source zero exactly. -/
@[simp]
theorem relativeFlag_obj_zero : (relativeFlag h hF A B α).diagram.obj 0 = A.diagram.obj 0 := rfl

/-- The actual initial inclusion is the identity of the original source zero. -/
@[simp]
theorem relativeFlagInclusion_app_zero :
    (relativeFlagInclusion h hF A B α).app 0 = 𝟙 (A.diagram.obj 0) := by
  change A.diagram.map ((finiteClampIso n).inv.app 0) ≫ 𝟙 _ = 𝟙 _
  have he : (finiteClampIso n).inv.app (0 : Fin (n + 1)) = 𝟙 (0 : Fin (n + 1)) :=
    Subsingleton.elim _ _
  rw [he]
  change A.diagram.map (𝟙 (0 : Fin (n + 1))) ≫ 𝟙 (A.diagram.obj 0) = 𝟙 (A.diagram.obj 0)
  rw [A.diagram.map_id, Category.id_comp]

/-- The actual initial projection is the original zero comparison. -/
@[simp]
theorem relativeFlagProjection_app_zero :
    (relativeFlagProjection h hF A B α).app 0 = α.app 0 := by
  change α.app 0 ≫ B.diagram.map ((finiteClampIso n).hom.app 0) = α.app 0
  have he : (finiteClampIso n).hom.app (0 : Fin (n + 1)) = 𝟙 (0 : Fin (n + 1)) :=
    Subsingleton.elim _ _
  rw [he, B.diagram.map_id, Category.comp_id]

/-- The weak projection is an actual morphism in the existing weak-flag category. -/
def relativeFlagComparison : (hF.weakFlagFunctor n).obj (relativeFlag h hF A B α) ⟶ B :=
  ⟨relativeFlagProjection h hF A B α, relativeFlagProjection_weak h hF A B α⟩

include h in
/-- App2 for all finite flags, with actual natural transformations and equations. -/
theorem exists_relativeFlag :
    ∃ (A' : WeakFlag W.cof W.weq n) (i : A.diagram ⟶ A'.diagram)
      (p : (hF.weakFlagFunctor n).obj A' ⟶ B),
      (∀ k, W.cof (i.app k)) ∧
        Functor.whiskerRight i F ≫ p.val = α ∧ A'.diagram.obj 0 = A.diagram.obj 0 :=
  ⟨relativeFlag h hF A B α, relativeFlagInclusion h hF A B α,
    relativeFlagComparison h hF A B α, relativeFlagInclusion_cof h hF A B α,
    relativeFlag_factorization h hF A B α, rfl⟩

/-- When α is weak, the source transformation in its App2 factorization is weak. -/
theorem relativeFlagInclusion_weak [V.weq.HasTwoOutOfThreeProperty]
    (hα : ∀ k, V.weq (α.app k)) (k : Fin (n + 1)) :
    W.weq ((relativeFlagInclusion h hF A B α).app k) := by
  apply h.reflects
  apply V.weq.of_postcomp _ ((relativeFlagProjection h hF A B α).app k)
    (relativeFlagProjection_weak h hF A B α k)
  have he := congrArg (fun η ↦ η.app k) (relativeFlag_factorization h hF A B α)
  change F.map ((relativeFlagInclusion h hF A B α).app k) ≫
    (relativeFlagProjection h hF A B α).app k = α.app k at he
  rw [he]
  exact hα k

end CategoryTheory.Waldhausen.HasApproximationProperty
