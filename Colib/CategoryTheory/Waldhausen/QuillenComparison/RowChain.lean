/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.Indices
public import Colib.CategoryTheory.Waldhausen.Rows.Faithful
public import Colib.CategoryTheory.QConstruction.Core

/-! # The original weak rows and their central Q-chains

The source is the existing pointwise weak quotient-row category, not a new
presentation of rows. The functor retains the original central quotient spans.
Adapted from Quillen/Waldhausen/QuillenComparison/RowSimplicial.lean and
RowFaithful.lean at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactCategory.ExactStructure C) {n : SimplexCategory}

/-- A natural isomorphism gives an original pointwise weak row morphism. -/
def weakRowHomOfIso {F G : WeakRows (ofExactCategory E) n} (e : F.obj.obj ≅ G.obj.obj) :
    F ⟶ G :=
  ⟨(objects (ofExactCategory E) n).homMk e.hom, fun p ↦ by
    change IsIso (e.hom.app p)
    infer_instance⟩

@[simp] theorem weakRowIso_weakRowHomOfIso {F G : WeakRows (ofExactCategory E) n}
    (e : F.obj.obj ≅ G.obj.obj) : weakRowIso E (weakRowHomOfIso E e) = e := by
  apply Iso.ext
  rfl
end CategoryTheory.Waldhausen.QuotientRows

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows SSet

/-- The central nested intervals of the genuine reversed edgewise ordinal. -/
def centralIntervalFunctor (n : SimplexCategory) :
    Fin (n.len + 1) ⥤ NestedInterval (EdgewiseSubdivision.ε.obj n) where
  obj := centralInterval n
  map f := homOfLE ⟨lowerIndex_antitone n (leOfHom f), upperIndex_monotone n (leOfHom f)⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactCategory.ExactStructure C)

/-- The prescribed central-interval comparison on the original weak rows. -/
def rowChainComparison (n : SimplexCategory) :
    WeakRows (ofExactCategory E) (EdgewiseSubdivision.ε.obj n) ⥤
      Core (ComposableArrows (QConstruction E.deflation E.inflation) n.len) where
  obj F := ⟨centralIntervalFunctor n ⋙ intervalQFunctor E F.obj⟩
  map e := ⟨Functor.isoWhiskerLeft (centralIntervalFunctor n) (intervalQFunctorIso E e)⟩
  map_id F := by
    apply Core.hom_ext
    ext p
    change (E.qIsoOfIso ((weakRowIso E (𝟙 F)).app _)).hom = 𝟙 _
    rw [weakRowIso_id]
    rfl
  map_comp e f := by
    apply Core.hom_ext
    ext p
    change (E.qIsoOfIso ((weakRowIso E (e ≫ f)).app _)).hom =
      (E.qIsoOfIso ((weakRowIso E e).app _)).hom ≫
        (E.qIsoOfIso ((weakRowIso E f).app _)).hom
    rw [weakRowIso_comp]
    change (E.qIsoOfIso ((weakRowIso E e).app _ ≪≫ (weakRowIso E f).app _)).hom = _
    rw [ExactCategory.ExactStructure.qIsoOfIso_trans, Iso.trans_hom]

@[simp] theorem lowerIndex_last (n : SimplexCategory) : lowerIndex n (Fin.last n.len) = 0 := by
  apply Fin.ext
  simp [lowerIndex, OrdinalJoin.left]

@[simp] theorem upperIndex_last (n : SimplexCategory) :
    upperIndex n (Fin.last n.len) = Fin.last (EdgewiseSubdivision.ε.obj n).len := by
  apply Fin.ext
  simp [upperIndex, OrdinalJoin.right, EdgewiseSubdivision.ε, OrdinalJoin.joinObj]
  omega

/-- The actual central Q-chain detects every original weak row morphism. -/
instance rowChainComparison_faithful (n : SimplexCategory) :
    (rowChainComparison E n).Faithful where
  map_injective {F G} e f h := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply rowNatTrans_ext_top E (F := F.obj) (G := G.obj)
    have hq := congrArg (fun a ↦ a.iso.hom.app (Fin.last n.len)) h
    change (E.qIsoOfIso ((weakRowIso E e).app (interval (lowerIndex n (Fin.last n.len))
      (upperIndex n (Fin.last n.len)) _))).hom =
      (E.qIsoOfIso ((weakRowIso E f).app (interval (lowerIndex n (Fin.last n.len))
        (upperIndex n (Fin.last n.len)) _))).hom at hq
    have he := E.qIsoOfIso_injective (Iso.ext hq)
    have hh := congrArg Iso.hom he
    have hi : interval (lowerIndex n (Fin.last n.len)) (upperIndex n (Fin.last n.len))
        (lowerIndex_le_upperIndex n _ _) =
        interval 0 (Fin.last (EdgewiseSubdivision.ε.obj n).len) (Fin.zero_le _) :=
      Subtype.ext (Prod.ext (lowerIndex_last n) (upperIndex_last n))
    change e.hom.hom.app _ = f.hom.hom.app _ at hh
    rw [hi] at hh
    exact hh

end CategoryTheory.Waldhausen.QuillenComparison
