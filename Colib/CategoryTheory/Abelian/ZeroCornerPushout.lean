/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian

/-! # The structural extension axiom for genuine complex weak equivalences

Displayed cofiber squares give actual short exact sequences. Their homology
four-lemma proof supplies the middle quasi-isomorphism, including in inherited
full subcategories. The extension axiom is derived, not assumed.


Implementation provenance:
`Quillen/Aglib/CategoryTheory/Abelian/ZeroCornerPushout.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Limits

section Cofiber
variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B Q Z : C} {i : A ⟶ B} {z : A ⟶ Z} {q : B ⟶ Q} {t : Z ⟶ Q}
  (h : IsPushout i z q t) (hZ : IsZero Z)

include h hZ

/-- The composite in an actual zero-corner pushout vanishes. -/
theorem cofiber_comp_zero : i ≫ q = 0 := by
  rw [h.w, hZ.eq_of_tgt z 0, zero_comp]

/-- The displayed cofiber is the actual categorical cokernel. -/
def cofiberIsCokernel : IsColimit (CokernelCofork.ofπ q (cofiber_comp_zero h hZ)) := by
  refine CokernelCofork.IsColimit.ofπ q (cofiber_comp_zero h hZ)
    (fun a ha ↦ h.desc a (hZ.to_ _) (by rw [hZ.eq_of_tgt z 0, zero_comp]; exact ha)) ?_ ?_
  · intro W a ha
    exact h.inl_desc _ _ _
  · intro W a ha m hm
    apply h.hom_ext
    · rw [h.inl_desc]
      exact hm
    · exact hZ.eq_of_src _ _

/-- A monic cofibration and displayed zero-corner pushout give a short exact sequence. -/
theorem cofiber_shortExact [Mono i] :
    (ShortComplex.mk i q (cofiber_comp_zero h hZ)).ShortExact where
  mono_f := inferInstance
  epi_g := Cofork.IsColimit.epi (cofiberIsCokernel h hZ)
  exact := (ShortComplex.mk i q (cofiber_comp_zero h hZ)).exact_of_g_is_cokernel
    (cofiberIsCokernel h hZ)
end Cofiber

end CategoryTheory.Limits
