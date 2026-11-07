/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.InitialCut
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.SplitFiberZero
public import Colib.CategoryTheory.Waldhausen.Rows.OneRowIso

/-! # Canonical identification of the cutoff with the original first-object inclusion

Restrict to the actual first two vertices, use the genuine one-step row
isomorphism, and pull back along the original zero-tail collapse. Full
faithfulness only reflects this actual categorical isomorphism.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/InitialCutIso.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The original first two vertices of the one-longer row. -/
def firstPair (n : SimplexCategory) : ⦋1⦌ ⟶ addInitial.obj n :=
  SimplexCategory.Hom.mk {
    toFun i := ⟨i.val, by
      have hi := i.isLt; change i.val < 2 at hi; change i.val < n.len+1+1; omega⟩
    monotone' := fun _ _ h ↦ h }

@[simp] theorem fiberOrdinal_firstPair (n : SimplexCategory) :
    fiberOrdinal n ≫ firstPair n = cutIndex n := by
  ext i : 3
  change Fin (n.len+1+1) at i
  cases i using Fin.cases <;> rfl

/-- The original first genuine one-step row. -/
def firstRow (n : SimplexCategory) : Obj N n ⥤ QuotientRows.Obj V ⦋1⦌ :=
  forget N n ⋙ QuotientRows.reindex V (firstPair n)

@[simp] theorem firstRow_oneEvaluation (n : SimplexCategory) :
    firstRow N n ⋙ QuotientRows.oneEvaluation V = first N n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Pulling the actual first one-step row over the tail gives precisely the cutoff. -/
theorem firstRow_fiberOrdinal (n : SimplexCategory) :
    firstRow N n ⋙ QuotientRows.reindex V (fiberOrdinal n) = cutFunctor N n ⋙ forget N n := by
  change (forget N n ⋙ QuotientRows.reindex V (firstPair n)) ⋙
    QuotientRows.reindex V (fiberOrdinal n) = forget N n ⋙ QuotientRows.reindex V (cutIndex n)
  rw [Functor.assoc, ← QuotientRows.reindex_comp, fiberOrdinal_firstPair]

/-- The actual ambient zero/identity/zero isomorphism on the cutoff row. -/
def firstFiberCutAmbientIso (n : SimplexCategory) :
    (first N n ⋙ fiber N n) ⋙ forget N n ≅ cutFunctor N n ⋙ forget N n := by
  let R := QuotientRows.reindex V (fiberOrdinal n)
  have hL : (first N n ⋙ fiber N n) ⋙ forget N n =
      (firstRow N n ⋙ (QuotientRows.oneEvaluation V ⋙ QuotientRows.oneEmbedding V)) ⋙ R := by
    rw [← firstRow_oneEvaluation N n]
    rfl
  have hR : (firstRow N n ⋙ 𝟭 (QuotientRows.Obj V ⦋1⦌)) ⋙ R = cutFunctor N n ⋙ forget N n := by
    simpa only [Functor.comp_id] using firstRow_fiberOrdinal N n
  exact eqToIso hL ≪≫ Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (firstRow N n) (QuotientRows.oneRoundTripIso V)) R ≪≫ eqToIso hR

/-- The original first-object zero-tail inclusion is canonically the actual cutoff functor. -/
def firstFiberCutIso (n : SimplexCategory) : first N n ⋙ fiber N n ≅ cutFunctor N n :=
  ((Functor.whiskeringRight (Obj N n) (Obj N n) (QuotientRows.Obj V (addInitial.obj n))).obj
    (forget N n)).preimageIso (firstFiberCutAmbientIso N n)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
