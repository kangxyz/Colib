/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.GradingRange
public import Colib.CategoryTheory.Waldhausen.Cofinality.GradedRows
public import Colib.CategoryTheory.Waldhausen.Approximation.FiniteReplacement
public import Colib.CategoryTheory.Waldhausen.Rows.Completion

/-! # Genuine realization of finite grade differences

Choose actual representatives of the finitely many specified grades, connect
them by original zero arrows, replace that finite chain by the genuine source
cofibration construction, and take its actual cofiber completion. Original
weak comparisons preserve every grade, so all specified differences are
realized. Surjectivity onto the actual value subgroup is already constructed.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GradeRealizability.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.QuotientRows


noncomputable section
open Topology SSet
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Cofinality.Grading
open QuotientRows
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- Every actual zero object has zero grade, without strict chosen-zero equality. -/
theorem value_of_isZero {Z : C} (hZ : IsZero Z) : d.value Z = 0 :=
  (d.weak (W.isZero.iso hZ).hom (W.weq_iso _ inferInstance)).symm.trans d.zero

/-- An actual row's interval grade is the difference of its two initial interval grades. -/
theorem rowValue_difference (n : SimplexCategory) (R : Obj d.coarseStructure n)
    (p : Interval n) :
    d.rowValue n R p = d.rowValue n R (interval 0 p.val.2 (Fin.zero_le _)) -
      d.rowValue n R (interval 0 p.val.1 (Fin.zero_le _)) := by
  have h := d.pushout (R.property.cofibration 0 p.val.1 p.val.2 (Fin.zero_le _) p.property)
    (R.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property)
  rw [d.value_of_isZero (R.property.zero p.val.1), add_zero] at h
  exact h

variable (T : FunctorialFactorization W) (hs : Function.Surjective d.value)
include T hs

/-- Actual finite replacement and cofiber completion realize every prescribed finite difference. -/
theorem exists_rowValue_difference (n : SimplexCategory) (a : Fin (n.len + 1) → G) :
    ∃ R : Obj d.coarseStructure n, d.rowValue n R = fun p ↦ a p.val.2 - a p.val.1 := by
  let obj (i : Fin (n.len + 1)) : C := (hs (a i)).choose
  let F : ComposableArrows C n.len := ComposableArrows.mkOfObjOfMapSucc obj
    (fun i ↦ W.isZero.from_ (obj i.castSucc) ≫ W.isZero.to_ (obj i.succ))
  let F' := (T.finiteReplacement n.len).obj F
  have hF' {i j : Fin (n.len + 1)} (f : i ⟶ j) : d.coarseStructure.cof (F'.map f) :=
    T.finiteReplacement_map_cof n.len F f
  let R := completeCofibrationFlag d.coarseStructure F' hF'
  have hval (i : Fin (n.len + 1)) : d.value (F'.obj i) = a i :=
    (d.weak (((T.finiteProjection n.len).app F).app i)
      (T.finiteProjection_weak n.len F i)).trans (hs (a i)).choose_spec
  refine ⟨R, ?_⟩
  funext p
  change d.value (R.obj.obj p) = _
  rw [d.cofiber_value (hF' (homOfLE p.property))
    (completionQuotient_isPushout d.coarseStructure F' hF' p), hval, hval]

end CategoryTheory.Waldhausen.Cofinality.Grading
