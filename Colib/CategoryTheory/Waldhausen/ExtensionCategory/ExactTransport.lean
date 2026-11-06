/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExactFunctor

/-! # Exact-functor transport with independent category universes -/
/-! Adapted from `Quillen.Waldhausen.ExtensionCategory.ExactTransport`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Structural exactness transfers across an actual natural isomorphism;
source and target object/hom universes need not agree. -/
theorem isExact_of_natIso (V : Structure C) (W : Structure D) {F G : C ⥤ D}
    (hF : IsExact V.cof V.weq W.cof W.weq F) (e : F ≅ G) : IsExact V.cof V.weq W.cof W.weq G where
  zero hZ := (hF.zero hZ).of_iso (e.app _).symm
  cofibration f hf := by
    have hm : G.map f = (e.app _).inv ≫ F.map f ≫ (e.app _).hom := by
      change G.map f = e.inv.app _ ≫ (F.map f ≫ e.hom.app _)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact W.cof.comp_mem _ _ (W.cof_iso _ inferInstance)
      (W.cof.comp_mem _ _ (hF.cofibration f hf) (W.cof_iso _ inferInstance))
  weak f hf := by
    have hm : G.map f = (e.app _).inv ≫ F.map f ≫ (e.app _).hom := by
      change G.map f = e.inv.app _ ≫ (F.map f ≫ e.hom.app _)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance)
      (W.weq.comp_mem _ _ (hF.weak f hf) (W.weq_iso _ inferInstance))
  pushout hi h := (hF.pushout hi h).of_iso (e.app _) (e.app _) (e.app _) (e.app _)
    (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _)

end CategoryTheory.Waldhausen.ExtensionCategory
