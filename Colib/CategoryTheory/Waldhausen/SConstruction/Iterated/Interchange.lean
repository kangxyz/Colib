/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Category
public import Colib.CategoryTheory.Waldhausen.Rows.Interchange

/-!
# Actual higher-row interchange and insertion compatibility

Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/Interchange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, ordinal parameters, chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet

/-- The genuine Reedy row transpose preserves the displayed zero row literally. -/
def rowSwap (W : WideSubcategory preservesZero.{u}) (m n : SimplexCategory) :
    (rows m).obj ((rows n).obj W) ≅ (rows n).obj ((rows m).obj W) where
  hom := ⟨⟨QuotientRows.transposeRows W.obj.waldhausen m n,
    QuotientRows.transposeRows_exact W.obj.waldhausen m n⟩, rfl⟩
  inv := ⟨⟨QuotientRows.transposeRows W.obj.waldhausen n m,
    QuotientRows.transposeRows_exact W.obj.waldhausen n m⟩, rfl⟩
  hom_inv_id := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact QuotientRows.transposeRows_twice W.obj.waldhausen m n
  inv_hom_id := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact QuotientRows.transposeRows_twice W.obj.waldhausen n m

/-- Actual row transpose is natural in the original exact zero-preserving functor. -/
def rowsInterchange (m n : SimplexCategory) : rows n ⋙ rows m ≅ rows m ⋙ rows n :=
  NatIso.ofComponents (fun W ↦ rowSwap W m n) (by
    intro V W F
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl))

/-- Move a fixed original row direction through the whole genuine simplicial row diagram. -/
def rowDiagramInterchange (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    rowDiagram ((rows n).obj W) ≅ rowDiagram W ⋙ rows n :=
  NatIso.ofComponents (fun m ↦ rowSwap W m.unop n) (by
    intro m m' α
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact QuotientRows.transposeRows_reindex_outer W.obj.waldhausen α.unop)

set_option maxHeartbeats 800000 in
-- The row-transpose equality exhausts the default 200000 heartbeats at `whnf`.
/-- At the original one-step row, transposition retains the full actual row. -/
lemma oneEmbedding_rowSwap (W : WideSubcategory preservesZero.{u}) (m : SimplexCategory) :
    QuotientRows.postcompose W.obj.waldhausen
      (QuotientRows.waldhausenStructure W.obj.waldhausen ⦋1⦌)
      (QuotientRows.oneEmbedding_exact W.obj.waldhausen) m ⋙
      QuotientRows.transposeRows W.obj.waldhausen m ⦋1⦌ =
        QuotientRows.oneEmbedding (QuotientRows.waldhausenStructure W.obj.waldhausen m) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro A
    apply ObjectProperty.FullSubcategory.ext
    refine CategoryTheory.Functor.ext ?_ ?_
    · rintro ⟨⟨i,j⟩,hij⟩
      fin_cases i <;> fin_cases j <;> rfl
    · rintro ⟨⟨i,j⟩,hij⟩ ⟨⟨k,l⟩,hkl⟩ f
      change i.val ≤ j.val at hij
      change k.val ≤ l.val at hkl
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
      all_goals first
        | exact (QuotientRows.isZero W.obj.waldhausen m).eq_of_src _ _
        | exact (QuotientRows.isZero W.obj.waldhausen m).eq_of_tgt _ _
        | omega
        | simp only [QuotientRows.oneEmbedding, QuotientRows.postcompose,
            QuotientRows.oneDiagram, QuotientRows.oneIndex, QuotientRows.oneChain,
            ComposableArrows.mk₂, QuotientRows.transposeRows, QuotientRows.transposeDiagram,
            Functor.comp_obj, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
            eqToHom_refl, Category.comp_id, Category.id_comp]
      all_goals apply ObjectProperty.hom_ext; ext q; rfl
  · intro A B f
    apply ObjectProperty.hom_ext
    ext p q
    rcases p with ⟨⟨i,j⟩,hij⟩
    fin_cases i <;> fin_cases j
    all_goals first
      | exact W.obj.waldhausen.isZero.eq_of_src _ _
      | simp [QuotientRows.oneEmbedding, QuotientRows.postcompose, QuotientRows.oneDiagram,
          QuotientRows.oneIndex, QuotientRows.oneChain, ComposableArrows.mk₂,
          ObjectProperty.FullSubcategory.comp_hom, QuotientRows.transposeRows]

/-- The new direction's one-row insertion is unchanged after the actual coordinate swap. -/
lemma insertion_rowSwap (W : WideSubcategory preservesZero.{u}) (m : SimplexCategory)
    {n : SimplexCategory}
    (τ : n ⟶ ⦋1⦌) :
    (rows m).map ((insertion τ).app W) ≫ (rowSwap W m n).hom =
      (insertion τ).app ((rows m).obj W) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  change QuotientRows.postcompose W.obj.waldhausen
      (QuotientRows.waldhausenStructure W.obj.waldhausen n)
    ((QuotientRows.oneEmbedding_exact W.obj.waldhausen).comp
      (QuotientRows.reindex_exact W.obj.waldhausen τ)) m ⋙
    QuotientRows.transposeRows W.obj.waldhausen m n =
    QuotientRows.oneEmbedding (QuotientRows.waldhausenStructure W.obj.waldhausen m) ⋙
      QuotientRows.reindex (QuotientRows.waldhausenStructure W.obj.waldhausen m) τ
  rw [← QuotientRows.postcompose_comp_postcompose W.obj.waldhausen _
    (QuotientRows.oneEmbedding_exact W.obj.waldhausen)
    _ (QuotientRows.reindex_exact W.obj.waldhausen τ) m]
  rw [CategoryTheory.Functor.assoc, QuotientRows.transposeRows_reindex_inner,
    ← CategoryTheory.Functor.assoc, oneEmbedding_rowSwap]


end CategoryTheory.Waldhausen.IteratedS
