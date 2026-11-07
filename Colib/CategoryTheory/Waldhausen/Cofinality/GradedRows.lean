/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.Grading
public import Colib.CategoryTheory.EqualGrade
public import Colib.CategoryTheory.Waldhausen.Rows.NervePresentation
public import Colib.CategoryTheory.Waldhausen.Rows.Structure

/-! # Actual graded quotient rows and their discrete realization models

The target consists of grade functions realized by genuine original quotient
rows. Its surjectivity is proved from this exact range, not assumed for arbitrary
tuples. Original row weakness is precisely equality of these functions, so zero
natural transformations give an actual row homotopy equivalence. Reindexing
keeps the original interval map. Identification of the realized grades with a
group nerve is a further combinatorial step.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GradedRows.lean`
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

/-- All original interval grades of a genuine quotient row. -/
def rowValue (n : SimplexCategory) (X : Obj d.coarseStructure n) : Interval n → G :=
  fun p ↦ d.value (X.obj.obj p)

/-- Only actually realizable original row grades are taken as the discrete target. -/
def RowGrade (n : SimplexCategory) := Set.range (d.rowValue n)

/-- The literal grade of every original row, with its actual realizability witness. -/
def rowGrade (n : SimplexCategory) (X : Obj d.coarseStructure n) : d.RowGrade n :=
  ⟨d.rowValue n X, ⟨X, rfl⟩⟩

/-- Surjectivity uses actual original representatives rather than arbitrary grade tuples. -/
theorem rowGrade_surjective (n : SimplexCategory) : Function.Surjective (d.rowGrade n) := by
  rintro ⟨_, X, rfl⟩
  exact ⟨X, rfl⟩

/-- Actual weak row arrows are exactly those with equal original interval grades. -/
theorem rowWeak_iff {n : SimplexCategory} {X Y : Obj d.coarseStructure n} (f : X ⟶ Y) :
    (waldhausenStructure d.coarseStructure n).weq f ↔ d.rowGrade n X = d.rowGrade n Y := by
  change (∀ p, d.value (X.obj.obj p) = d.value (Y.obj.obj p)) ↔ _
  rw [Subtype.ext_iff]
  exact funext_iff.symm

/-- Original weak rows project to their actually realized discrete grade. -/
def rowProjection (n : SimplexCategory) : WeakRows d.coarseStructure n ⥤ Discrete (d.RowGrade n) :=
  EqualGrade.projectionOfIff (d.rowGrade n) (waldhausenStructure d.coarseStructure n).weq
    d.rowWeak_iff

/-- The actual zero transformations give a genuine homotopy equivalence on every original row. -/
def rowProjectionHomotopyEquiv (n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (WeakRows d.coarseStructure n))
      (ClassifyingSpace (Discrete (d.RowGrade n))) := by
  letI : HasZeroMorphisms (Obj d.coarseStructure n) := (isZero d.coarseStructure n).hasZeroMorphisms
  exact EqualGrade.projectionOfIffHomotopyEquiv (d.rowGrade n) (d.rowGrade_surjective n)
    (waldhausenStructure d.coarseStructure n).weq d.rowWeak_iff

/-- The original row grade projection is literally the forward realized comparison. -/
@[simp] theorem rowProjectionHomotopyEquiv_toFun (n : SimplexCategory) :
    (d.rowProjectionHomotopyEquiv n).toFun = (classifyingSpaceMap (d.rowProjection n)).hom :=
  by
    let : HasZeroMorphisms (Obj d.coarseStructure n) := (isZero d.coarseStructure
      n).hasZeroMorphisms
    exact EqualGrade.projectionOfIffHomotopyEquiv_toFun _ _ _ _

/-- Restrict a realized grade using exactly the original interval-index functor. -/
def reindexGrade {m n : SimplexCategory} (α : m ⟶ n) (a : d.RowGrade n) : d.RowGrade m :=
  ⟨fun p ↦ a.val ((indexMap α).obj p), by
    obtain ⟨X, hX⟩ := a.property
    refine ⟨(reindex d.coarseStructure α).obj X, ?_⟩
    exact congrArg (fun f ↦ fun p ↦ f ((indexMap α).obj p)) hX⟩

/-- Actual original row reindexing has the literal reindexed grade. -/
@[simp] theorem rowGrade_reindex {m n : SimplexCategory} (α : m ⟶ n) (X : Obj d.coarseStructure n) :
    d.rowGrade m ((reindex d.coarseStructure α).obj X) = d.reindexGrade α (d.rowGrade n X) := rfl

/-- The genuine simplicial set of realizable original row grades. -/
def gradeSSet : SSet.{u} where
  obj n := d.RowGrade n.unop
  map α := TypeCat.ofHom (d.reindexGrade α.unop)
  map_id n := by apply ConcreteCategory.hom_ext; intro a; apply Subtype.ext; rfl
  map_comp α β := by apply ConcreteCategory.hom_ext; intro a; apply Subtype.ext; rfl

end CategoryTheory.Waldhausen.Cofinality.Grading
