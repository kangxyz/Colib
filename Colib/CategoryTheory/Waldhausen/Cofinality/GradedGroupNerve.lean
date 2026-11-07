/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.GradeRealizability
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Tactic.Abel

/-! # Realized grade rows as the genuine group nerve

Finite cofibration replacement and actual cofiber completion realize every
chain of group grades, provided the grades have actual object representatives.
The isomorphism retains the original interval values as original nerve arrows.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GradedGroupNerve.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.QuotientRows


noncomputable section
open Topology SSet
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Cofinality.Grading
open QuotientRows
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- Every realized diagonal interval grade vanishes by its actual zero object. -/
theorem rowGrade_diagonal {n : SimplexCategory} (a : d.RowGrade n) (i : Fin (n.len + 1)) :
    a.val (interval i i le_rfl) = 0 := by
  obtain ⟨R, hR⟩ := a.property
  rw [← hR]
  exact d.value_of_isZero (R.property.zero i)

/-- Actual quotient squares enforce the additive interval relation. -/
theorem rowGrade_add {n : SimplexCategory} (a : d.RowGrade n)
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    a.val (interval i k (hij.trans hjk)) = a.val (interval i j hij) + a.val (interval j k hjk) := by
  obtain ⟨R, hR⟩ := a.property
  rw [← hR]
  rw [d.rowValue_difference n R (interval i k (hij.trans hjk)),
    d.rowValue_difference n R (interval i j hij), d.rowValue_difference n R (interval j k hjk)]
  dsimp only [interval]
  abel

/-- The actual original interval grades are the arrows of a chain in the group category. -/
def rowGradeChain (n : SimplexCategory) (a : d.RowGrade n) :
    ComposableArrows (SingleObj (Multiplicative G)) n.len where
  obj _ := SingleObj.star _
  map {i j} f := Multiplicative.ofAdd (a.val (interval i j (leOfHom f)))
  map_id i := by
    change Multiplicative.ofAdd (a.val (interval i i le_rfl)) = 1
    rw [d.rowGrade_diagonal]
    rfl
  map_comp {i j k} f g := by
    change Multiplicative.ofAdd (a.val (interval i k (leOfHom (f ≫ g)))) =
      Multiplicative.ofAdd (a.val (interval j k (leOfHom g))) *
        Multiplicative.ofAdd (a.val (interval i j (leOfHom f)))
    rw [d.rowGrade_add a i j k (leOfHom f) (leOfHom g)]
    exact congrArg Multiplicative.ofAdd (add_comm _ _)

/-- Group-nerve initial arrows determine each original interval arrow by subtraction. -/
theorem groupChain_difference {n : SimplexCategory}
    (F : ComposableArrows (SingleObj (Multiplicative G)) n.len) (p : Interval n) :
    Multiplicative.toAdd (F.map (homOfLE p.property)) =
      Multiplicative.toAdd (F.map (homOfLE (Fin.zero_le p.val.2))) -
        Multiplicative.toAdd (F.map (homOfLE (Fin.zero_le p.val.1))) := by
  have h := congrArg Multiplicative.toAdd
    (F.map_comp (homOfLE (Fin.zero_le p.val.1)) (homOfLE p.property))
  change Multiplicative.toAdd (F.map (homOfLE (Fin.zero_le p.val.2))) =
    Multiplicative.toAdd (F.map (homOfLE p.property)) +
      Multiplicative.toAdd (F.map (homOfLE (Fin.zero_le p.val.1))) at h
  rw [h]
  abel

variable (T : FunctorialFactorization W) (hs : Function.Surjective d.value)

/-- Every actual group-nerve chain is realized by an original quotient row. -/
def chainRowGrade {n : SimplexCategory}
    (F : ComposableArrows (SingleObj (Multiplicative G)) n.len) : d.RowGrade n :=
  ⟨fun p ↦ Multiplicative.toAdd (F.map (homOfLE p.property)), by
    obtain ⟨R, hR⟩ := d.exists_rowValue_difference T hs n
      (fun i ↦ Multiplicative.toAdd (F.map (homOfLE (Fin.zero_le i))))
    refine ⟨R, ?_⟩
    funext p
    exact (congrFun hR p).trans (groupChain_difference F p).symm⟩

/-- Actual realized row grades and group-nerve chains are equivalent in every dimension. -/
def rowGradeChainEquiv (n : SimplexCategory) :
    d.RowGrade n ≃ ComposableArrows (SingleObj (Multiplicative G)) n.len where
  toFun := d.rowGradeChain n
  invFun := d.chainRowGrade T hs
  left_inv _ := rfl
  right_inv F := by
    apply CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)

/-- The strict simplicial identification with the genuine one-object group nerve. -/
def gradeGroupNerveIso : d.gradeSSet ≅ nerve (SingleObj (Multiplicative G)) :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso (d.rowGradeChainEquiv T hs n.unop)) (by
    intro n m α
    ext a : 3
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl))

end CategoryTheory.Waldhausen.Cofinality.Grading
