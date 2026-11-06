/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Tail
public import Colib.CategoryTheory.Waldhausen.Rows.OneRow

/-! # The actual constant zero-tail split-fiber inclusion

The added vertex maps to0 and every original tail vertex maps to1. Reindexing
the literal one-step row gives the original object on every initial
nondegenerate interval and the actual chosen zero on its entire tail.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/SplitFiber.lean`
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

/-- Collapse all original tail vertices to1, retaining the added vertex0. -/
def fiberOrdinal (n : SimplexCategory) : addInitial.obj n ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk {
    toFun := Fin.cases 0 (fun _ ↦ 1)
    monotone' := by
      intro i j h
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => have h' : i.val + 1 ≤ 0 := h; omega
        | succ _ => exact le_rfl }

@[simp] theorem fiberOrdinal_zero (n : SimplexCategory) : (fiberOrdinal n).toOrderHom 0 = 0 := rfl
@[simp] theorem fiberOrdinal_succ (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (fiberOrdinal n).toOrderHom i.succ = 1 := rfl

/-- The collapse is strictly natural for every original relative ordinal map. -/
@[simp] theorem fiberOrdinal_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    addInitial.map α ≫ fiberOrdinal n = fiberOrdinal m := by
  ext i : 3
  cases i using Fin.cases <;> rfl

/-- The original one-step row pulled back to all initial intervals. -/
def fiberUnderlying (n : SimplexCategory) : C ⥤ QuotientRows.Obj V (addInitial.obj n) :=
  QuotientRows.oneEmbedding V ⋙ QuotientRows.reindex V (fiberOrdinal n)

/-- Every actual tail object is the chosen zero, hence genuinely coarse-acyclic. -/
theorem fiberUnderlying_mem (n : SimplexCategory) (X : C) :
    objects N n ((fiberUnderlying (V := V) n).obj X) := by
  intro p
  exact acyclic_of_isZero N.coarse V.isZero

/-- The actual constant split-fiber inclusion into relative quotient rows. -/
def fiber (n : SimplexCategory) : C ⥤ Obj N n :=
  (objects N n).lift (fiberUnderlying (V := V) n) (fiberUnderlying_mem N n)

@[simp] theorem fiber_forget (n : SimplexCategory) :
    fiber N n ⋙ forget N n = fiberUnderlying (V := V) n := rfl

/-- Exactness follows from the actual one-step embedding and actual ordinal restriction. -/
theorem fiber_exact (n : SimplexCategory) :
    IsExact V.cof V.weq (waldhausenStructure N n).cof
      (waldhausenStructure N n).weq (fiber N n) where
  zero h := IsZero.of_full_of_faithful_of_isZero (forget N n) _
    (((QuotientRows.oneEmbedding_exact V).comp (QuotientRows.reindex_exact V (fiberOrdinal
      n))).zero h)
  cofibration f hf :=
    ((QuotientRows.oneEmbedding_exact V).comp (QuotientRows.reindex_exact V (fiberOrdinal
      n))).cofibration f hf
  weak f hf :=
    ((QuotientRows.oneEmbedding_exact V).comp (QuotientRows.reindex_exact V (fiberOrdinal
      n))).weak f hf
  pushout hf h := IsPushout.of_map_of_faithful (forget N n)
    (((QuotientRows.oneEmbedding_exact V).comp (QuotientRows.reindex_exact V (fiberOrdinal
      n))).pushout hf h)

/-- The original first quotient is literally the original object and morphism. -/
@[simp] theorem fiber_first (n : SimplexCategory) : fiber N n ⋙ first N n = 𝟭 C := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The entire actual acyclic tail is the chosen constant zero row. -/
@[simp] theorem fiber_tail (n : SimplexCategory) :
    fiber N n ⋙ tailFunctor N n =
      (Functor.const C).obj (QuotientRows.zero (acyclicStructure N) n) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual split-fiber inclusion is strictly natural under every outer ordinal map. -/
@[simp] theorem fiber_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    fiber N n ⋙ reindex N α = fiber N m := by
  apply functor_eq_of_comp_forget N
  change QuotientRows.oneEmbedding V ⋙
      (QuotientRows.reindex V (fiberOrdinal n) ⋙ QuotientRows.reindex V (addInitial.map α)) =
    QuotientRows.oneEmbedding V ⋙ QuotientRows.reindex V (fiberOrdinal m)
  rw [← QuotientRows.reindex_comp, fiberOrdinal_naturality]

/-- The exact split triangle retains both the original object and the literal zero tail. -/
@[simp] theorem fiber_firstTail (n : SimplexCategory) :
    fiber N n ⋙ firstTail N n =
      (𝟭 C).prod' ((Functor.const C).obj (QuotientRows.zero (acyclicStructure N) n)) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
