/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.Projective.Connecting

/-!
# Transporting a resolution cocycle to a connecting class

The resolution may resolve an object merely isomorphic to the quotient in a
short exact sequence. The comparison uses the actual inverse isomorphism in
Yoneda precomposition; neither a replacement resolution nor a new Ext model
is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe w

namespace CategoryTheory.ProjectiveResolution

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact) {X : C} (P : ProjectiveResolution X)
  (e : X ≅ S.X₃) (b : P.complex.X 0 ⟶ S.X₂) (c : P.complex.X 1 ⟶ S.X₁)
  (hc : P.complex.d 2 1 ≫ c = 0) (h : c ≫ S.f = P.complex.d 1 0 ≫ b)
  (hb : b ≫ S.g = P.π.f 0 ≫ e.hom)

include h hb in
/-- Inverse-isomorphism transport of a resolution cocycle retains the negative connecting class. -/
theorem mk₀_inv_comp_extMk_eq_neg_extClass :
    (Ext.mk₀ e.inv).comp (P.extMk c 2 rfl hc) (zero_add 1) = -hS.extClass := by
  let T : ShortComplex C := ShortComplex.mk S.f (S.g ≫ e.inv) (by simp)
  let i : T ≅ S := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
    (by simp [T]) (by simp [T])
  have hT : T.ShortExact := ShortComplex.shortExact_of_iso i.symm hS
  have hbT : b ≫ T.g = P.π.f 0 := by
    dsimp only [T]
    rw [← Category.assoc, hb]
    erw [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [P.extMk_eq_neg_extClass hT b c hc h hbT, Ext.comp_neg]
  congr 1
  have hn := hT.extClass_naturality hS i.hom
  change hT.extClass.comp (Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) =
    (Ext.mk₀ e.hom).comp hS.extClass (zero_add 1) at hn
  rw [Ext.comp_mk₀_id] at hn
  rw [hn, Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

end CategoryTheory.ProjectiveResolution
