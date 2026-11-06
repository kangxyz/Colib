/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Map
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Actual pointwise pushouts along pointwise cofibrations

Only the pushouts supplied by the Waldhausen axioms are used; the ambient
category is not assumed to have arbitrary pushouts or arbitrary colimits.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/PointwisePushouts.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]
/-- Displayed pointwise pushouts give an actual functor-category pushout. -/
theorem functor_isPushout_of_pointwise {A B D P : J ⥤ C}
    (f : A ⟶ B) (g : A ⟶ D) (i : B ⟶ P) (j : D ⟶ P)
    (hp : ∀ x, IsPushout (f.app x) (g.app x) (i.app x) (j.app x)) : IsPushout f g i j := by
  have w : f ≫ i = g ≫ j := by ext x; exact (hp x).w
  let d (s : PushoutCocone f g) : P ⟶ s.pt := {
    app x := (hp x).desc (s.inl.app x) (s.inr.app x) (congrArg (fun k ↦ k.app x) s.condition)
    naturality x y a := by
      apply (hp x).hom_ext
      · rw [← Category.assoc, ← i.naturality a, Category.assoc, (hp y).inl_desc,
          ← Category.assoc, (hp x).inl_desc]
        exact s.inl.naturality a
      · rw [← Category.assoc, ← j.naturality a, Category.assoc, (hp y).inr_desc,
          ← Category.assoc, (hp x).inr_desc]
        exact s.inr.naturality a }
  have hi (s : PushoutCocone f g) : i ≫ d s = s.inl := by ext x; exact (hp x).inl_desc _ _ _
  have hj (s : PushoutCocone f g) : j ≫ d s = s.inr := by ext x; exact (hp x).inr_desc _ _ _
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i j w)
  refine PushoutCocone.IsColimit.mk w d hi hj ?_
  intro s m hm hn
  ext x
  apply (hp x).hom_ext
  · exact (congrArg (fun k ↦ k.app x) hm).trans (congrArg (fun k ↦ k.app x) (hi s)).symm
  · exact (congrArg (fun k ↦ k.app x) hn).trans (congrArg (fun k ↦ k.app x) (hj s)).symm

variable (W : Structure C) {A B D : J ⥤ C} (f : A ⟶ B) (g : A ⟶ D)

/-- Every evaluation of this actual span has a colimit. -/
theorem hasColimit_evaluation (hf : ∀ x, W.cof (f.app x)) (x : J) :
    HasColimit ((span f g).flip.obj x) := by
  obtain ⟨P, i, j, h⟩ := W.pushout_exists (f.app x) (g.app x) (hf x)
  let : HasPushout (((evaluation J C).obj x).map f) (((evaluation J C).obj x).map g) := h.hasPushout
  change HasColimit (span f g ⋙ (evaluation J C).obj x)
  exact hasColimit_of_iso (spanCompIso ((evaluation J C).obj x) f g)

/-- The functor-category pushout exists and every component is an actual pushout. -/
theorem exists_pointwise_pushout (hf : ∀ x, W.cof (f.app x)) :
    ∃ (P : J ⥤ C) (i : B ⟶ P) (j : D ⟶ P), IsPushout f g i j ∧
      ∀ x, IsPushout (f.app x) (g.app x) (i.app x) (j.app x) := by
  let (x : J) : HasColimit ((span f g).flip.obj x) := hasColimit_evaluation W f g hf x
  refine ⟨pushout f g, pushout.inl f g, pushout.inr f g, .of_hasPushout _ _, ?_⟩
  intro x
  exact (IsPushout.of_hasPushout f g).map ((evaluation J C).obj x)

/-- Any displayed functor-category pushout along pointwise cofibrations is pointwise. -/
theorem pointwise_of_functor_isPushout (hf : ∀ x, W.cof (f.app x))
    {P : J ⥤ C} {i : B ⟶ P} {j : D ⟶ P} (h : IsPushout f g i j) (x : J) :
    IsPushout (f.app x) (g.app x) (i.app x) (j.app x) := by
  let (x : J) : HasColimit ((span f g).flip.obj x) := hasColimit_evaluation W f g hf x
  exact h.map ((evaluation J C).obj x)

end CategoryTheory.Waldhausen.QuotientRows
