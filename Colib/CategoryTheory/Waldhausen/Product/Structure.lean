/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.CategoryTheory.Products.Basic

/-! # Actual product Waldhausen categories

The product structure and its exact functors are categorical constructions.
No statement about geometric realization preserving products is used.
-/
/-! Source: `Quillen/Waldhausen/ExtensionCategory/Product.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universes are retained.
The S-product isomorphism is not a normalized or strict S-model comparison. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Product
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Actual componentwise pushouts are pushouts in the product category. -/
theorem product_isPushout {A B E P : C × D} (f : A ⟶ B) (g : A ⟶ E) (i : B ⟶ P) (j : E ⟶ P)
    (h₁ : IsPushout f.1 g.1 i.1 j.1) (h₂ : IsPushout f.2 g.2 i.2 j.2) : IsPushout f g i j := by
  have w : f ≫ i = g ≫ j := _root_.Prod.ext h₁.w h₂.w
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i j w)
  refine PushoutCocone.IsColimit.mk w
    (fun s ↦ (h₁.desc s.inl.1 s.inr.1 (congrArg _root_.Prod.fst s.condition),
      h₂.desc s.inl.2 s.inr.2 (congrArg _root_.Prod.snd s.condition))) ?_ ?_ ?_
  · intro s
    exact _root_.Prod.ext (h₁.inl_desc _ _ _) (h₂.inl_desc _ _ _)
  · intro s
    exact _root_.Prod.ext (h₁.inr_desc _ _ _) (h₂.inr_desc _ _ _)
  · intro s m hm hn
    apply _root_.Prod.ext
    · apply h₁.hom_ext
      · exact (congrArg _root_.Prod.fst hm).trans (h₁.inl_desc _ _ _).symm
      · exact (congrArg _root_.Prod.fst hn).trans (h₁.inr_desc _ _ _).symm
    · apply h₂.hom_ext
      · exact (congrArg _root_.Prod.snd hm).trans (h₂.inl_desc _ _ _).symm
      · exact (congrArg _root_.Prod.snd hn).trans (h₂.inr_desc _ _ _).symm

/-- Product projection preserves every displayed pushout. -/
theorem fst_isPushout {A B E P : C × D} {f : A ⟶ B} {g : A ⟶ E} {i : B ⟶ P} {j : E ⟶ P}
    (h : IsPushout f g i j) : IsPushout f.1 g.1 i.1 j.1 := by
  have w := congrArg _root_.Prod.fst h.w
  have w₂ : f.2 ≫ i.2 = g.2 ≫ j.2 := congrArg _root_.Prod.snd h.w
  let d (s : PushoutCocone f.1 g.1) : P ⟶ (s.pt, P.2) :=
    h.desc (s.inl, i.2) (s.inr, j.2) (by
      apply _root_.Prod.ext
      · exact s.condition
      · exact w₂)
  have hi (s : PushoutCocone f.1 g.1) : i ≫ d s = (s.inl, i.2) := h.inl_desc _ _ _
  have hj (s : PushoutCocone f.1 g.1) : j ≫ d s = (s.inr, j.2) := h.inr_desc _ _ _
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i.1 j.1 w)
  refine PushoutCocone.IsColimit.mk w (fun s ↦ (d s).1)
    (fun s ↦ congrArg _root_.Prod.fst (hi s)) (fun s ↦ congrArg _root_.Prod.fst (hj s)) ?_
  intro s m hm hn
  have he : ((m, 𝟙 P.2) : P ⟶ (s.pt, P.2)) = d s := by
    apply h.hom_ext
    · exact (_root_.Prod.ext hm (Category.comp_id _)).trans (hi s).symm
    · exact (_root_.Prod.ext hn (Category.comp_id _)).trans (hj s).symm
  exact congrArg _root_.Prod.fst he

/-- The second product projection also preserves every displayed pushout. -/
theorem snd_isPushout {A B E P : C × D} {f : A ⟶ B} {g : A ⟶ E} {i : B ⟶ P} {j : E ⟶ P}
    (h : IsPushout f g i j) : IsPushout f.2 g.2 i.2 j.2 := by
  have w := congrArg _root_.Prod.snd h.w
  have w₁ : f.1 ≫ i.1 = g.1 ≫ j.1 := congrArg _root_.Prod.fst h.w
  let d (s : PushoutCocone f.2 g.2) : P ⟶ (P.1, s.pt) :=
    h.desc (i.1, s.inl) (j.1, s.inr) (by
      apply _root_.Prod.ext
      · exact w₁
      · exact s.condition)
  have hi (s : PushoutCocone f.2 g.2) : i ≫ d s = (i.1, s.inl) := h.inl_desc _ _ _
  have hj (s : PushoutCocone f.2 g.2) : j ≫ d s = (j.1, s.inr) := h.inr_desc _ _ _
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i.2 j.2 w)
  refine PushoutCocone.IsColimit.mk w (fun s ↦ (d s).2)
    (fun s ↦ congrArg _root_.Prod.snd (hi s)) (fun s ↦ congrArg _root_.Prod.snd (hj s)) ?_
  intro s m hm hn
  have he : ((𝟙 P.1, m) : P ⟶ (P.1, s.pt)) = d s := by
    apply h.hom_ext
    · exact (_root_.Prod.ext (Category.comp_id _) hm).trans (hi s).symm
    · exact (_root_.Prod.ext (Category.comp_id _) hn).trans (hj s).symm
  exact congrArg _root_.Prod.snd he

/-- Pairs of genuine zero objects are zero in the product category. -/
theorem product_isZero {X : C} {Y : D} (hX : IsZero X) (hY : IsZero Y) : IsZero (X, Y) where
  unique_to Z := by
    refine ⟨{ default := (hX.to_ Z.1, hY.to_ Z.2), uniq := ?_ }⟩
    intro f
    exact _root_.Prod.ext (hX.eq_of_src _ _) (hY.eq_of_src _ _)
  unique_from Z := by
    refine ⟨{ default := (hX.from_ Z.1, hY.from_ Z.2), uniq := ?_ }⟩
    intro f
    exact _root_.Prod.ext (hX.eq_of_tgt _ _) (hY.eq_of_tgt _ _)

/-- The componentwise product Waldhausen structure. -/
def productStructure (V : Structure C) (W : Structure D) : Structure (C × D) where
  zero := (V.zero, W.zero)
  isZero := product_isZero V.isZero W.isZero
  cof := MorphismProperty.prod V.cof W.cof
  weq := MorphismProperty.prod V.weq W.weq
  cof_multiplicative := {
    id_mem X := ⟨V.cof.id_mem X.1, W.cof.id_mem X.2⟩
    comp_mem f g hf hg := ⟨V.cof.comp_mem _ _ hf.1 hg.1, W.cof.comp_mem _ _ hf.2 hg.2⟩ }
  weq_multiplicative := {
    id_mem X := ⟨V.weq.id_mem X.1, W.weq.id_mem X.2⟩
    comp_mem f g hf hg := ⟨V.weq.comp_mem _ _ hf.1 hg.1, W.weq.comp_mem _ _ hf.2 hg.2⟩ }
  cof_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact ⟨V.cof_iso _ (inferInstance : IsIso ((CategoryTheory.Prod.fst C D).map f)),
      W.cof_iso _ (inferInstance : IsIso ((CategoryTheory.Prod.snd C D).map f))⟩
  weq_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact ⟨V.weq_iso _ (inferInstance : IsIso ((CategoryTheory.Prod.fst C D).map f)),
      W.weq_iso _ (inferInstance : IsIso ((CategoryTheory.Prod.snd C D).map f))⟩
  cof_zero X := by
    have h : (product_isZero V.isZero W.isZero).to_ X = (V.isZero.to_ X.1, W.isZero.to_ X.2) :=
      (product_isZero V.isZero W.isZero).eq_of_src _ _
    rw [h]
    exact ⟨V.cof_zero X.1, W.cof_zero X.2⟩
  pushout_exists f g hf := by
    obtain ⟨P, i, j, h⟩ := V.pushout_exists f.1 g.1 hf.1
    obtain ⟨Q, k, l, h'⟩ := W.pushout_exists f.2 g.2 hf.2
    exact ⟨(P, Q), (i, k), (j, l), product_isPushout _ _ _ _ h h'⟩
  cof_pushout hf h := ⟨V.cof_pushout hf.1 (fst_isPushout h), W.cof_pushout hf.2 (snd_isPushout h)⟩
  gluing := by
    intro A B E P A' B' E' P' f g i j f' g' i' j' a b d p hf hf' h h' ef eg ei ej ha hb hd
    exact ⟨V.gluing a.1 b.1 d.1 p.1 hf.1 hf'.1 (fst_isPushout h) (fst_isPushout h')
      (congrArg _root_.Prod.fst ef) (congrArg _root_.Prod.fst eg)
      (congrArg _root_.Prod.fst ei) (congrArg _root_.Prod.fst ej) ha.1 hb.1 hd.1,
      W.gluing a.2 b.2 d.2 p.2 hf.2 hf'.2 (snd_isPushout h) (snd_isPushout h')
      (congrArg _root_.Prod.snd ef) (congrArg _root_.Prod.snd eg)
      (congrArg _root_.Prod.snd ei) (congrArg _root_.Prod.snd ej) ha.2 hb.2 hd.2⟩

theorem fst_exact (V : Structure C) (W : Structure D) :
    IsExact (productStructure V W).cof (productStructure V W).weq V.cof V.weq
      (CategoryTheory.Prod.fst C D) where
  zero h := V.isZero.of_iso ((CategoryTheory.Prod.fst C D).mapIso (h.iso (product_isZero
    V.isZero W.isZero)))
  cofibration _ h := h.1
  weak _ h := h.1
  pushout _ h := fst_isPushout h

theorem snd_exact (V : Structure C) (W : Structure D) :
    IsExact (productStructure V W).cof (productStructure V W).weq W.cof W.weq
      (CategoryTheory.Prod.snd C D) where
  zero h := W.isZero.of_iso ((CategoryTheory.Prod.snd C D).mapIso (h.iso (product_isZero
    V.isZero W.isZero)))
  cofibration _ h := h.2
  weak _ h := h.2
  pushout _ h := snd_isPushout h

variable {E : Type*} [Category* E]
theorem pair_exact (U : Structure E) (V : Structure C) (W : Structure D) {F : E ⥤ C} {G : E ⥤ D}
    (hF : IsExact U.cof U.weq V.cof V.weq F) (hG : IsExact U.cof U.weq W.cof W.weq G) :
    IsExact U.cof U.weq (productStructure V W).cof (productStructure V W).weq (F.prod' G) where
  zero h := product_isZero (hF.zero h) (hG.zero h)
  cofibration f h := ⟨hF.cofibration f h, hG.cofibration f h⟩
  weak f h := ⟨hF.weak f h, hG.weak f h⟩
  pushout hf h := product_isPushout _ _ _ _ (hF.pushout hf h) (hG.pushout hf h)

end CategoryTheory.Waldhausen.Product
