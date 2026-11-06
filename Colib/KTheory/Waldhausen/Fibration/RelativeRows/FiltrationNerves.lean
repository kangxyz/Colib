/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.WeakInterchange
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.FiltrationClassifying
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ExtensionAxiom
public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.RowPostcompose
public import Colib.CategoryTheory.Waldhausen.Rows.NerveFunctoriality

/-! # Original relative inner rows as fine-weak cofibration-chain nerves

The forward map first transposes the original quotient rows and then reads
the original initial filtration. Both categorical equivalences are proved
separately. Their actual composite is natural in both original row indices.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/FiltrationNerves.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse)

/-- The unchanged relative-row transpose followed by the original initial filtration. -/
def innerSFiltration (m n : SimplexCategory) :
    QuotientRows.WeakRows (waldhausenStructure N n) m ⥤
      FineWeakChains (RowWeakEquivalences.nested N m) n :=
  innerSWeakInterchange N m n ⋙ weakFiltrationPresentation (RowWeakEquivalences.nested N m)
    (RowWeakEquivalences.extensionAxiom N he m) n

/-- The original component is the initial interval in the original relative row. -/
@[simp] theorem innerSFiltration_obj_component (m n : SimplexCategory)
    (F : QuotientRows.WeakRows (waldhausenStructure N n) m)
    (i : Fin (n.len + 1)) (p : Interval m) :
    (((innerSFiltration N he m n).obj F).obj.obj.obj i).obj.obj p =
      (F.obj.obj.obj p).obj.obj.obj (interval 0 i.succ (Fin.zero_le _)) := rfl

/-- Actual composite categorical equivalence, with that literal forward functor. -/
def innerSFiltrationEquivalence (m n : SimplexCategory) :
    QuotientRows.WeakRows (waldhausenStructure N n) m ≌
      FineWeakChains (RowWeakEquivalences.nested N m) n :=
  (innerSWeakEquivalence N m n).trans
    (weakFiltrationEquivalence (RowWeakEquivalences.nested N m)
      (RowWeakEquivalences.extensionAxiom N he m) n)

@[simp] theorem innerSFiltrationEquivalence_functor (m n : SimplexCategory) :
    (innerSFiltrationEquivalence N he m n).functor = innerSFiltration N he m n := rfl

/-- The original forward classifying map has a genuine continuous homotopy inverse. -/
def innerSFiltrationClassifyingHomotopyEquiv (m n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (QuotientRows.WeakRows (waldhausenStructure N
      n) m))
      (ClassifyingSpace (FineWeakChains (RowWeakEquivalences.nested N m) n)) :=
  equivalenceClassifyingHomotopyEquiv (innerSFiltrationEquivalence N he m n)

@[simp] theorem innerSFiltrationClassifyingHomotopyEquiv_toFun (m n : SimplexCategory) :
    (innerSFiltrationClassifyingHomotopyEquiv N he m n).toFun =
      (classifyingSpaceMap (innerSFiltration N he m n)).hom := rfl

/-- The relative ordinal direction acts on the same original chain by restriction. -/
theorem innerSFiltration_relative_reindex (m : SimplexCategory)
    {n n' : SimplexCategory} (α : n' ⟶ n) :
    QuotientRows.weakRowsPostcompose (waldhausenStructure N n) (waldhausenStructure N n')
        (reindex_exact N α) m ⋙ innerSFiltration N he m n' =
      innerSFiltration N he m n ⋙ MixedNerves.fineWeakCofReindex (RowWeakEquivalences.nested N
        m) α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The inner S direction acts by literal original quotient-row restriction. -/
theorem innerSFiltration_inner_reindex (n : SimplexCategory)
    {m m' : SimplexCategory} (α : m' ⟶ m) :
    QuotientRows.weakRowsReindex (waldhausenStructure N n) α ⋙ innerSFiltration N he m' n =
      innerSFiltration N he m n ⋙ MixedNerves.fineWeakCofPostcompose
        (MixedNerves.rowReindexCompatible N α) n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Fine-weak chain nerves in the original inner-S direction for a fixed relative degree. -/
def innerFiltrationNerve (n : SimplexCategory) : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} where
  obj m := nerve (FineWeakChains (RowWeakEquivalences.nested N m.unop) n)
  map α := nerveMap (MixedNerves.fineWeakCofPostcompose (MixedNerves.rowReindexCompatible N
    α.unop) n)
  map_id m := by
    change nerveMap (MixedNerves.fineWeakCofPostcompose (MixedNerves.rowReindexCompatible N (𝟙
      m.unop)) n) = _
    rw [MixedNerves.rowReindexCompatible_id]
    ext k F
    rfl
  map_comp α β := by
    change nerveMap (MixedNerves.fineWeakCofPostcompose (MixedNerves.rowReindexCompatible N
      (β.unop ≫ α.unop)) n) = _
    rw [MixedNerves.rowReindexCompatible_comp]
    ext k F
    rfl

/-- The proved original filtration equivalences give a genuine bisimplicial forward map. -/
def innerFiltrationNerveMap (n : SimplexCategory) :
    QuotientRows.weakRowNerve (waldhausenStructure N n) ⟶ innerFiltrationNerve N n where
  app m := nerveMap (innerSFiltration N he m.unop n)
  naturality m m' α := by
    ext k F : 4
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
