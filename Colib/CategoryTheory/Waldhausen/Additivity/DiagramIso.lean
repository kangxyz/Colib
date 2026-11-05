/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Bisimplicial

/-! # Actual S-diagrams are invariant under natural isomorphism

Implementation provenance: `Quillen/Waldhausen/Additivity/DiagramIso.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v

namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Natural isomorphism preserves every structural condition of an actual
S-diagram, including its displayed quotient pushouts. -/
theorem simplex₂_of_iso {n m : SimplexCategory} {A B : Grid₂ n m ⥤ C}
    (hA : IsSimplex₂ W.cof W.weq A) (e : A ≅ B) : IsSimplex₂ W.cof W.weq B where
  zero t i := (hA.zero t i).of_iso (e.app _).symm
  cofibration t i j k hij hjk := by
    have hm {x y : Grid₂ n m} (f : x ⟶ y) :
        B.map f = e.inv.app x ≫ A.map f ≫ e.hom.app y := by
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact W.cof.comp_mem _ _ (W.cof_iso _ (by infer_instance))
      (W.cof.comp_mem _ _ (hA.cofibration t i j k hij hjk) (W.cof_iso _ (by infer_instance)))
  quotient t i j k hij hjk := (hA.quotient t i j k hij hjk).of_iso
    (e.app _) (e.app _) (e.app _) (e.app _)
    (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _)
  weak s t i j hst hij := by
    have hm {x y : Grid₂ n m} (f : x ⟶ y) :
        B.map f = e.inv.app x ≫ A.map f ≫ e.hom.app y := by
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact W.weq.comp_mem _ _ (W.weq_iso _ (by infer_instance))
      (W.weq.comp_mem _ _ (hA.weak s t i j hst hij) (W.weq_iso _ (by infer_instance)))

end CategoryTheory.Waldhausen.Additivity
