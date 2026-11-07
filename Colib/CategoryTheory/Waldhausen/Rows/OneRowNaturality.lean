/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.OneRow
public import Colib.CategoryTheory.Waldhausen.Rows.Functoriality


/-!
# Exact functors and the genuine one-step quotient row

The original three objects `0, X, 0` and every original arrow are preserved
by an exact functor which preserves the chosen zero object. The chosen-zero
equality is explicit; no automatic strict compatibility is inferred from
ordinary preservation of zero objects. Object and morphism universes are independent.

Implementation provenance: `Quillen/Waldhausen/SConstruction/Rows/OneRowNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v u' v'
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F) (h0 : F.obj V.zero = W.zero)

include hF h0

lemma oneDiagram_postcompose (X : C) : oneDiagram V X ⋙ F = oneDiagram W (F.obj X) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · rintro ⟨⟨i,j⟩,hij⟩
    fin_cases i <;> fin_cases j
    · exact h0
    · rfl
    · rfl
    · exact h0
  · rintro ⟨⟨i,j⟩,hij⟩ ⟨⟨k,l⟩,hkl⟩ f
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
    all_goals first
      | exact (hF.zero V.isZero).eq_of_src _ _
      | exact (hF.zero V.isZero).eq_of_tgt _ _
      | simp [oneDiagram, oneIndex, oneChain, ComposableArrows.mk₂]

lemma oneEmbedding_postcompose :
    oneEmbedding V ⋙ postcompose V W hF ⦋1⦌ = F ⋙ oneEmbedding W := by
  refine CategoryTheory.Functor.ext (fun X ↦ ObjectProperty.FullSubcategory.ext
    (oneDiagram_postcompose V W hF h0 X)) ?_
  intro X Y f
  apply ObjectProperty.hom_ext
  ext p
  rcases p with ⟨⟨i,j⟩,hij⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hF.zero V.isZero).eq_of_src _ _
    | simp [oneEmbedding, postcompose, oneDiagram, oneIndex,
        oneChain, ComposableArrows.mk₂, ObjectProperty.FullSubcategory.comp_hom]

end CategoryTheory.Waldhausen.QuotientRows
