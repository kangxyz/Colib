/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Double
public import Colib.CategoryTheory.Waldhausen.Rows.OneRowNaturality
public import Colib.CategoryTheory.Waldhausen.Rows.PostcomposeExact

/-!
# Strict-zero exact functors and iterated quotient rows

These original row calculations precede their realized loop-map consumer.
Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/Functoriality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, zero equality, exactness assumptions and universes are unchanged.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory SSet
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F) (h0 : F.obj V.zero = W.zero)

include h0 in
lemma suspensionRow_postcompose {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    suspensionRow V τ ⋙ QuotientRows.postcompose V W hF n = F ⋙ suspensionRow W τ := by
  change (QuotientRows.oneEmbedding V ⋙ QuotientRows.reindex V τ) ⋙ _ = _
  rw [Functor.assoc, ← QuotientRows.postcompose_reindex V W hF τ,
    ← Functor.assoc, QuotientRows.oneEmbedding_postcompose V W hF h0]
  rfl

include h0 in
lemma postcompose_zero (n : SimplexCategory) :
    (QuotientRows.postcompose V W hF n).obj (QuotientRows.zero V n) =
      QuotientRows.zero W n := by
  apply ObjectProperty.FullSubcategory.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ h0) ?_
  intro p q f
  exact (hF.zero V.isZero).eq_of_src _ _

end CategoryTheory.Waldhausen.IteratedS
