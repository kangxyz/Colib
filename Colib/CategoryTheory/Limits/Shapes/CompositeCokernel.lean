/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Limits.Shapes.CokernelPushout
public import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Quotient calculus used to complete admissible flags

All squares and quotient maps below are proved using actual cokernel
universal properties. No ambient abelian category or global choice of
quotients compatible with simplicial operators is required.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (w : f ≫ g = h)
variable [HasCokernel f] [HasCokernel g] [HasCokernel h]

/-- The induced inclusion of the first quotient into the composite quotient. -/
def quotientInclusion : cokernel f ⟶ cokernel h :=
  cokernel.map f h (𝟙 A) g (by simpa using w)

/-- The quotient by the first quotient. -/
def quotientProjection : cokernel h ⟶ cokernel g :=
  cokernel.map h g f (𝟙 D) (by simpa using w.symm)

omit [HasCokernel g] in
@[reassoc (attr := simp)]
theorem π_quotientInclusion : cokernel.π f ≫ quotientInclusion f g h w = g ≫ cokernel.π h :=
  cokernel.π_desc _ _ _

omit [HasCokernel f] in
@[reassoc (attr := simp)]
theorem π_quotientProjection : cokernel.π h ≫ quotientProjection f g h w = cokernel.π g := by
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

omit [HasCokernel g] in
/-- The quotient inclusion is an actual cobase change of the original map. -/
theorem quotient_isPushout : IsPushout g (cokernel.π f) (cokernel.π h)
    (quotientInclusion f g h w) := by
  have hsq : g ≫ cokernel.π h = cokernel.π f ≫ quotientInclusion f g h w :=
    (π_quotientInclusion f g h w).symm
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hsq)
  refine PushoutCocone.IsColimit.mk hsq
    (fun s ↦ cokernel.desc h s.inl (by
      rw [← w, Category.assoc, s.condition, ← Category.assoc, cokernel.condition, zero_comp]))
        ?_ ?_ ?_
  · intro s
    exact cokernel.π_desc _ _ _
  · intro s
    apply (cancel_epi (cokernel.π f)).1
    rw [← Category.assoc, π_quotientInclusion, Category.assoc, cokernel.π_desc, s.condition]
  · intro s m hm _
    apply (cancel_epi (cokernel.π h)).1
    exact hm.trans (cokernel.π_desc _ _ _).symm

@[reassoc (attr := simp)]
theorem quotient_comp_zero : quotientInclusion f g h w ≫ quotientProjection f g h w = 0 := by
  apply (cancel_epi (cokernel.π f)).1
  rw [← Category.assoc, π_quotientInclusion, Category.assoc, π_quotientProjection,
    cokernel.condition, comp_zero]

/-- Quotienting twice gives the cokernel of the original second map. -/
def quotientIsCokernel : IsColimit (CokernelCofork.ofπ (quotientProjection f g h w)
    (quotient_comp_zero f g h w)) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {W} a ha ↦ cokernel.desc g (cokernel.π h ≫ a) (by
      rw [← Category.assoc, ← π_quotientInclusion f g h w, Category.assoc, ha, comp_zero])) ?_ ?_
  · intro W a ha
    apply (cancel_epi (cokernel.π h)).1
    rw [← Category.assoc, π_quotientProjection, cokernel.π_desc]
  · intro W a ha m hm
    apply (cancel_epi (cokernel.π g)).1
    rw [cokernel.π_desc, ← π_quotientProjection f g h w, Category.assoc, hm]

end CategoryTheory.Limits
