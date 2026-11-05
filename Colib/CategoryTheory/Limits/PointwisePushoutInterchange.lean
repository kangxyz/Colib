/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Interchange of actual pushout squares

A pointwise pushout of three diagrams carries any square which is a pushout
in each of those diagrams to a pushout. All universal properties are supplied
only for the displayed squares; no global cocompleteness assumption is used.


Implementation provenance: `Quillen/Aglib/CategoryTheory/Limits/PointwisePushoutInterchange.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v'

namespace CategoryTheory.Limits

variable {J : Type u} [Category.{v} J] {D : Type u'} [Category.{v'} D]
variable {H F G P : J ⥤ D}
variable (a : H ⟶ F) (b : H ⟶ G) (i : F ⟶ P) (j : G ⟶ P)
variable (hs : ∀ X, IsPushout (a.app X) (b.app X) (i.app X) (j.app X))
variable {A B C Q : J} (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ Q) (k : C ⟶ Q)
variable (w : f ≫ h = g ≫ k)
variable (hH : IsPushout (H.map f) (H.map g) (H.map h) (H.map k))
variable (hF : IsPushout (F.map f) (F.map g) (F.map h) (F.map k))
variable (hG : IsPushout (G.map f) (G.map g) (G.map h) (G.map k))

include hs hH hF hG w in
/-- Pushouts commute with the displayed pointwise pushouts, proved from the
actual four universal properties. -/
theorem isPushout_of_pointwise_pushouts :
    IsPushout (P.map f) (P.map g) (P.map h) (P.map k) := by
  have wp : P.map f ≫ P.map h = P.map g ≫ P.map k := by
    rw [← P.map_comp, ← P.map_comp, w]
  let dF (s : PushoutCocone (P.map f) (P.map g)) : F.obj Q ⟶ s.pt :=
    hF.desc (i.app B ≫ s.inl) (i.app C ≫ s.inr) (by
      rw [i.naturality_assoc f, i.naturality_assoc g, s.condition])
  let dG (s : PushoutCocone (P.map f) (P.map g)) : G.obj Q ⟶ s.pt :=
    hG.desc (j.app B ≫ s.inl) (j.app C ≫ s.inr) (by
      rw [j.naturality_assoc f, j.naturality_assoc g, s.condition])
  have hd (s : PushoutCocone (P.map f) (P.map g)) :
      a.app Q ≫ dF s = b.app Q ≫ dG s := by
    apply hH.hom_ext
    · rw [a.naturality_assoc h, b.naturality_assoc h]
      simp only [dF, dG, IsPushout.inl_desc, ← Category.assoc, (hs B).w]
    · rw [a.naturality_assoc k, b.naturality_assoc k]
      simp only [dF, dG, IsPushout.inr_desc, ← Category.assoc, (hs C).w]
  let d (s : PushoutCocone (P.map f) (P.map g)) := (hs Q).desc (dF s) (dG s) (hd s)
  have hi (s : PushoutCocone (P.map f) (P.map g)) : P.map h ≫ d s = s.inl := by
    apply (hs B).hom_ext
    · rw [← Category.assoc, ← i.naturality h, Category.assoc]
      simp only [d, IsPushout.inl_desc, dF, IsPushout.inl_desc]
    · rw [← Category.assoc, ← j.naturality h, Category.assoc]
      simp only [d, IsPushout.inr_desc, dG, IsPushout.inl_desc]
  have hj (s : PushoutCocone (P.map f) (P.map g)) : P.map k ≫ d s = s.inr := by
    apply (hs C).hom_ext
    · rw [← Category.assoc, ← i.naturality k, Category.assoc]
      simp only [d, IsPushout.inl_desc, dF, IsPushout.inr_desc]
    · rw [← Category.assoc, ← j.naturality k, Category.assoc]
      simp only [d, IsPushout.inr_desc, dG, IsPushout.inr_desc]
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ wp)
  refine PushoutCocone.IsColimit.mk wp d hi hj ?_
  intro s m hm hn
  apply (hs Q).hom_ext
  · apply hF.hom_ext
    · rw [← Category.assoc, i.naturality h, Category.assoc, hm,
        ← Category.assoc, i.naturality h, Category.assoc, hi]
    · rw [← Category.assoc, i.naturality k, Category.assoc, hn,
        ← Category.assoc, i.naturality k, Category.assoc, hj]
  · apply hG.hom_ext
    · rw [← Category.assoc, j.naturality h, Category.assoc, hm,
        ← Category.assoc, j.naturality h, Category.assoc, hi]
    · rw [← Category.assoc, j.naturality k, Category.assoc, hn,
        ← Category.assoc, j.naturality k, Category.assoc, hj]

end CategoryTheory.Limits
