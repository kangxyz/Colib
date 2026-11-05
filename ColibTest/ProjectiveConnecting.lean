/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Abelian.Projective.Connecting

open CategoryTheory CategoryTheory.Abelian

universe w

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (P : ProjectiveResolution S.X₃) (hS : S.ShortExact)
  (b : P.complex.X 0 ⟶ S.X₂) (c : P.complex.X 1 ⟶ S.X₁)
  (hc : P.complex.d 2 1 ≫ c = 0) (h : c ≫ S.f = P.complex.d 1 0 ≫ b)
  (hb : b ≫ S.g = P.π.f 0)

example : P.extMk c 2 rfl hc = -hS.extClass :=
  P.extMk_eq_neg_extClass hS b c hc h hb

-- The comparison retains arbitrary coefficients and native Yoneda postcomposition.
example {Y : C} (g : S.X₁ ⟶ Y) :
    P.extMk (c ≫ g) 2 rfl (by simp [reassoc_of% hc]) =
      -(hS.extClass.comp (Ext.mk₀ g) (add_zero 1)) := by
  rw [← P.extMk_comp_mk₀ c 2 rfl hc g, P.extMk_eq_neg_extClass hS b c hc h hb,
    Ext.neg_comp]
