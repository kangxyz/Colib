/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
Adapted from `Quillen/Topology/LocalCoefficients/CoproductColimits.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the native singular
chain complex, actual transition maps, and coefficient transports.

# Colimits of coproducts indexed over a fixed label space

A type-valued cocone labels each index by a point of its cocone. Give each
label an object of a category with coproducts. The resulting diagram of
coproducts has as colimit the coproduct over the label space whenever the
original type cocone is colimiting. This is proved by descending dependent
families of morphisms, with every equality transport explicit.
-/

@[expose] public section

open CategoryTheory Limits
noncomputable section
universe u v
namespace CategoryTheory.Limits.ReindexedCoproduct
variable {J : Type u} [SmallCategory J] (F : J ⥤ Type u) (c : Cocone F)
  {C : Type v} [Category.{u} C] [HasCoproducts.{u} C] (M : c.pt → C)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem label_eq {j k : J} (a : j ⟶ k) (x : F.obj j) :
    c.ι.app j x = c.ι.app k (F.map a x) :=
  (ConcreteCategory.congr_hom (c.w a) x).symm

theorem ι_congr {S : Type u} (N : S → C) {x y : S} (h : x = y) :
    eqToHom (congrArg N h) ≫ Sigma.ι N y = Sigma.ι N x := by
  subst y
  simp

theorem ι_heq {S : Type u} (N : S → C) {x y : S} (h : x = y) :
    HEq (Sigma.ι N x) (Sigma.ι N y) := by
  subst y
  rfl

/-- Reindex a fixed family of coefficient objects along all stage labels. -/
def diagram : J ⥤ C where
  obj j := ∐ fun x : F.obj j ↦ M (c.ι.app j x)
  map {j k} a := Sigma.desc fun x ↦
    eqToHom (congrArg M (label_eq F c a x)) ≫
      Sigma.ι (fun y : F.obj k ↦ M (c.ι.app k y)) (F.map a x)
  map_id j := by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_desc, Category.comp_id]
    apply eq_of_heq
    exact (eqToHom_comp_heq _ _).trans
      (ι_heq (fun y ↦ M (c.ι.app j y)) (F.map_id_apply j x))
  map_comp {j k l} a b := by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_desc, Sigma.ι_desc_assoc, Category.assoc,
      eqToHom_trans_assoc]
    apply eq_of_heq
    exact (eqToHom_comp_heq _ _).trans
      ((ι_heq (fun y ↦ M (c.ι.app l y)) (F.map_comp_apply a b x)).trans
        (eqToHom_comp_heq _ _).symm)

/-- The original label maps induce the comparison to the target coproduct. -/
def cocone : Cocone (diagram F c M) where
  pt := ∐ M
  ι :=
    { app j := Sigma.desc fun x ↦ Sigma.ι M (c.ι.app j x)
      naturality {j k} a := by
        apply Sigma.hom_ext
        intro x
        simp only [diagram, Sigma.ι_desc_assoc, Sigma.ι_desc,
          Category.assoc, Functor.const_obj_map]
        exact (ι_congr M (label_eq F c a x)).trans (Category.comp_id _).symm }

/-- Compatible morphisms retain their coefficient label during descent. -/
def descentCocone (s : Cocone (diagram F c M)) : Cocone F where
  pt := Σ x : c.pt, M x ⟶ s.pt
  ι :=
    { app j := ↾fun x ↦ ⟨c.ι.app j x,
        Sigma.ι (fun y : F.obj j ↦ M (c.ι.app j y)) x ≫ s.ι.app j⟩
      naturality {j k} a := by
        ext x
        apply Sigma.ext (label_eq F c a x).symm
        have h := congrArg (fun t ↦
          Sigma.ι (fun y : F.obj j ↦ M (c.ι.app j y)) x ≫ t) (s.w a)
        simp only [diagram, Sigma.ι_desc_assoc, Category.assoc] at h
        exact (eqToHom_comp_heq _ _).symm.trans (heq_of_eq h) }

variable (hc : IsColimit c)

/-- Descend the dependent family through the actual type colimit. -/
def descendedFamily (s : Cocone (diagram F c M)) : c.pt → Σ x : c.pt, M x ⟶ s.pt :=
  hc.desc (descentCocone F c M s)

theorem descendedFamily_stage (s : Cocone (diagram F c M)) (j : J) (x : F.obj j) :
    descendedFamily F c M hc s (c.ι.app j x) =
      ⟨c.ι.app j x, Sigma.ι (fun y : F.obj j ↦ M (c.ι.app j y)) x ≫ s.ι.app j⟩ :=
  ConcreteCategory.congr_hom (hc.fac (descentCocone F c M s) j) x

theorem descendedFamily_label (s : Cocone (diagram F c M)) (x : c.pt) :
    (descendedFamily F c M hc s x).1 = x := by
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective_of_isColimit hc x
  rw [descendedFamily_stage]

/-- The universal map from the target coproduct. -/
def desc (s : Cocone (diagram F c M)) : (∐ M) ⟶ s.pt :=
  Sigma.desc fun x ↦ eqToHom (congrArg M (descendedFamily_label F c M hc s x).symm) ≫
    (descendedFamily F c M hc s x).2

theorem desc_fac (s : Cocone (diagram F c M)) (j : J) :
    (cocone F c M).ι.app j ≫ desc F c M hc s = s.ι.app j := by
  apply Sigma.hom_ext
  intro x
  simp only [cocone, desc, Sigma.ι_desc_assoc, Sigma.ι_desc]
  apply eq_of_heq
  apply (eqToHom_comp_heq _ _).trans
  exact (Sigma.mk.inj_iff.mp (descendedFamily_stage F c M hc s j x)).2

/-- Coproduct reindexing over a fixed target family preserves the given type colimit. -/
def isColimit : IsColimit (cocone F c M) where
  desc s := desc F c M hc s
  fac s j := desc_fac F c M hc s j
  uniq s m hm := by
    apply Sigma.hom_ext
    intro x
    obtain ⟨j, y, rfl⟩ := Types.jointly_surjective_of_isColimit hc x
    have h := congrArg (fun t ↦
      Sigma.ι (fun z : F.obj j ↦ M (c.ι.app j z)) y ≫ t)
      ((hm j).trans (desc_fac F c M hc s j).symm)
    simpa only [cocone, Sigma.ι_desc_assoc] using h

end CategoryTheory.Limits.ReindexedCoproduct
