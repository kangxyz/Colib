/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Approximation.SequenceReplacement
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Functorial replacement of finite flags

A finite flag is extended constantly beyond its final vertex, replaced by
the genuine functorial sequence construction, and restricted back. The
comparison is a natural transformation with objectwise weak equivalences.
Every replacement arrow is a cofibration and the initial vertex is unchanged.


Implementation provenance:
`Quillen/Waldhausen/Approximation/FiniteReplacement.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe v u

namespace CategoryTheory.Waldhausen.FunctorialFactorization

variable {C : Type u} [Category.{v} C] {W : Structure C}

/-- Include the finite ordered index set in the natural numbers. -/
def finiteIndex (n : ℕ) : Fin (n + 1) ⥤ ℕ :=
  (show Monotone (fun i : Fin (n + 1) ↦ (i : ℕ)) from fun _ _ h ↦ h).functor

/-- Extend a finite flag constantly past its last vertex. -/
def clampIndex (n : ℕ) : ℕ ⥤ Fin (n + 1) :=
  (show Monotone (fun k : ℕ ↦ (⟨min k n, by omega⟩ : Fin (n + 1))) from
    fun _ _ h ↦ min_le_min_right n h).functor

/-- Clamping after inclusion gives back each finite index. -/
def finiteClampIso (n : ℕ) : finiteIndex n ⋙ clampIndex n ≅ 𝟭 (Fin (n + 1)) :=
  NatIso.ofComponents (fun i ↦ eqToIso (by
      apply Fin.ext
      change min i.val n = i.val
      exact min_eq_left (Nat.le_of_lt_succ i.isLt)))
    (fun _ ↦ Subsingleton.elim _ _)

/-- Constant extension of finite diagrams. -/
def extendFinite (n : ℕ) : ComposableArrows C n ⥤ (ℕ ⥤ C) :=
  (whiskeringLeft ℕ (Fin (n + 1)) C).obj (clampIndex n)

/-- Restriction of natural-number diagrams to their first n+1 vertices. -/
def restrictFinite (n : ℕ) : (ℕ ⥤ C) ⥤ ComposableArrows C n :=
  (whiskeringLeft (Fin (n + 1)) ℕ C).obj (finiteIndex n)

/-- The canonical round-trip isomorphism on finite diagrams. -/
def finiteRoundTripIso (n : ℕ) : extendFinite (C := C) n ⋙ restrictFinite n ≅ 𝟭 _ :=
  NatIso.ofComponents (fun F ↦ isoWhiskerRight (finiteClampIso n) F) (by
    intro F G α
    ext i
    exact (α.naturality ((finiteClampIso n).hom.app i)).symm)

/-- A functorial cofibration replacement of every finite flag. -/
def finiteReplacement (D : FunctorialFactorization W) (n : ℕ) :
    ComposableArrows C n ⥤ ComposableArrows C n :=
  extendFinite n ⋙ sequenceReplacement D ⋙ restrictFinite n

/-- The actual natural comparison from the replacement to the original flag. -/
def finiteProjection (D : FunctorialFactorization W) (n : ℕ) :
    finiteReplacement D n ⟶ 𝟭 _ :=
  whiskerRight (whiskerLeft (extendFinite n) (sequenceProjection D)) (restrictFinite n) ≫
    (finiteRoundTripIso n).hom

/-- Every arrow in the replacement finite flag is a cofibration. -/
theorem finiteReplacement_map_cof (D : FunctorialFactorization W) (n : ℕ)
    (F : ComposableArrows C n) {i j : Fin (n + 1)} (f : i ⟶ j) :
    W.cof (((finiteReplacement D n).obj F).map f) :=
  sequenceReplacement_map_cof D ((extendFinite n).obj F) ((finiteIndex n).map f)

/-- The finite-flag projection is objectwise a weak equivalence. -/
theorem finiteProjection_weak (D : FunctorialFactorization W) (n : ℕ)
    (F : ComposableArrows C n) (i : Fin (n + 1)) :
    W.weq (((finiteProjection D n).app F).app i) := by
  change W.weq (((sequenceProjection D).app ((extendFinite n).obj F)).app i.val ≫
    ((finiteRoundTripIso n).hom.app F).app i)
  exact W.weq.comp_mem _ _ (sequenceProjection_weak D _ _)
    (W.weq_iso _ inferInstance)

/-- The initial vertex of a finite replacement is the original initial vertex. -/
theorem finiteReplacement_obj_zero (D : FunctorialFactorization W) (n : ℕ)
    (F : ComposableArrows C n) : ((finiteReplacement D n).obj F).obj 0 = F.obj 0 := by
  change F.obj ⟨min 0 n, _⟩ = F.obj 0
  congr 1

/-- Objectwise weak equivalences of finite flags remain objectwise weak
 equivalences after replacement. -/
theorem finiteReplacement_map_weak (D : FunctorialFactorization W)
    [W.weq.HasTwoOutOfThreeProperty] (n : ℕ) {F G : ComposableArrows C n} (α : F ⟶ G)
    (hα : ∀ i, W.weq (α.app i)) (i : Fin (n + 1)) :
    W.weq (((finiteReplacement D n).map α).app i) :=
  sequenceReplacement_map_weak D ((extendFinite n).map α)
    (fun k ↦ hα ((clampIndex n).obj k)) i.val

end CategoryTheory.Waldhausen.FunctorialFactorization
