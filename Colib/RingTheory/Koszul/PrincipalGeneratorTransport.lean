/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.Projective.ConnectingTransport
public import Colib.RingTheory.Koszul.PrincipalExtOne

/-!
# Principal generator comparison with explicit quotient transport

This interface applies directly to a supplied native projective resolution
of a presentation quotient `Q` and its actual isomorphism to `R/(a)`.
The transported coefficient cocycle is the negative of the standard
connecting class. All degree-zero and degree-one identifications are explicit.

The old Aglib `singleProjectiveResolution` and `singleQuotientIdealLinearEquiv`
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f` supply such data.
No old Aglib model is reintroduced here, and a compiled theorem directly
naming its `singleIdealExtOneClass` is not asserted by this file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (a : R) (ha : IsSMulRegular R a) {Q : ModuleCat.{u} R} (P : ProjectiveResolution Q)
  (e : Q ≅ ModuleCat.of R (R ⧸ Ideal.span {a}))
  (b : P.complex.X 0 ⟶ ModuleCat.of R R) (c : P.complex.X 1 ⟶ ModuleCat.of R R)
  (hc : P.complex.d 2 1 ≫ c = 0)
  (h : c ≫ ModuleCat.ofHom (LinearMap.lsmul R R a) = P.complex.d 1 0 ≫ b)
  (hb : b ≫ ModuleCat.ofHom (Ideal.span {a}).mkQ = P.π.f 0 ≫ e.hom)

include h hb in
/-- Actual quotient transport sends each coefficient cocycle to minus the standard class. -/
theorem principalExtMk_transport_eq_neg_class (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ e.inv).comp
      (P.extMk (c ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)) 2 rfl
        (by simp [reassoc_of% hc])) (zero_add 1) = -principalExtOneClass a ha N x := by
  have ht := P.mk₀_inv_comp_extMk_eq_neg_extClass
    (ModuleCat.principalShortComplex_shortExact a ha) e b c hc h hb
  have ht' := congrArg
    (fun z => z.comp (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)))
      (add_zero 1)) ht
  rw [Ext.comp_assoc_of_third_deg_zero, P.extMk_comp_mk₀, Ext.neg_comp] at ht'
  exact ht'

end Koszul

attribute [colib_tag "COL-0121"] Koszul.principalExtMk_transport_eq_neg_class
  CategoryTheory.ProjectiveResolution.mk₀_inv_comp_extMk_eq_neg_extClass

attribute [stacks 06XP "Ingredient: Yoneda composition; transport and sign proved here"]
  Koszul.principalExtMk_transport_eq_neg_class
