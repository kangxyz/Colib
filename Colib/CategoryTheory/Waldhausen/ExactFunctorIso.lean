/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.ExactFunctor

/-! # Exactness under natural isomorphism

The comparison uses actual isomorphism components and their naturality squares.
No chosen-basepoint rebasing or topology is needed at this layer.
Implementation provenance: adapted from `Quillen/Waldhausen/PointedFunctor.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This isolated draft has not been compiled.

-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Waldhausen

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {W' : Structure D}

instance Structure.cof_respectsIso (W : Structure C) : W.cof.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ h ↦ W.cof_iso _ h)

instance Structure.weq_respectsIso (W : Structure C) : W.weq.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ h ↦ W.weq_iso _ h)

/-- Exactness is preserved under natural isomorphism. -/
theorem IsExact.of_iso {F G : C ⥤ D} (hF : IsExact W.cof W.weq W'.cof W'.weq F)
    (e : F ≅ G) : IsExact W.cof W.weq W'.cof W'.weq G where
  zero hZ := (hF.zero hZ).of_iso (e.app _).symm
  cofibration f hf := by
    have hm : G.map f = (e.app _).inv ≫ F.map f ≫ (e.app _).hom := by
      change G.map f = e.inv.app _ ≫ (F.map f ≫ e.hom.app _)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact W'.cof.comp_mem _ _ (W'.cof_iso _ inferInstance)
      (W'.cof.comp_mem _ _ (hF.cofibration f hf) (W'.cof_iso _ inferInstance))
  weak f hf := by
    have hm : G.map f = (e.app _).inv ≫ F.map f ≫ (e.app _).hom := by
      change G.map f = e.inv.app _ ≫ (F.map f ≫ e.hom.app _)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact W'.weq.comp_mem _ _ (W'.weq_iso _ inferInstance)
      (W'.weq.comp_mem _ _ (hF.weak f hf) (W'.weq_iso _ inferInstance))
  pushout hi h := (hF.pushout hi h).of_iso (e.app _) (e.app _) (e.app _) (e.app _)
    (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _)

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0144",
  colib_ref "Waldhausen1985" "Sections 1.1-1.2, pp.320-321 and 326-327"
    "background" "Consequences of the axioms under natural isomorphism; no induced homotopy"]
  CategoryTheory.Waldhausen.Structure.cof_respectsIso
  CategoryTheory.Waldhausen.Structure.weq_respectsIso
  CategoryTheory.Waldhausen.IsExact.of_iso
