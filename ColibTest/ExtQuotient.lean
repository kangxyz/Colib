/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.DerivedCategory.Ext.Quotient

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (I : Ideal R) (N : ModuleCat.{u} R) (n : ℕ)

-- Arbitrary degree and Ext universe; no regularity or finiteness hypotheses.
example : Module.IsTorsionBySet R (Ext (ModuleCat.of R (R ⧸ I)) N n) I :=
  Ext.quotientSourceIsTorsionBySet I N n

example (r : R) (e : Ext (ModuleCat.of R (R ⧸ I)) N n) :
    letI := Ext.quotientSourceModule I N n
    Ideal.Quotient.mk I r • e = r • e :=
  Ext.quotientSourceModule_mk_smul I N n r e

example (b : R ⧸ I) (e : Ext (ModuleCat.of R (R ⧸ I)) N n) :
    letI := Ext.quotientSourceModule I N n
    b • e = (Ext.mk₀ (Ext.quotientSourceMul I b)).comp e (zero_add n) :=
  Ext.quotientSourceModule_smul_eq_precomp I N n b e

-- The explicit quotient action commutes with coefficient postcomposition.
example {N' : ModuleCat.{u} R} (g : N ⟶ N') (b : R ⧸ I)
    (e : Ext (ModuleCat.of R (R ⧸ I)) N n) :
    letI := Ext.quotientSourceModule I N n
    letI := Ext.quotientSourceModule I N' n
    (b • e).comp (Ext.mk₀ g) (add_zero n) =
      b • e.comp (Ext.mk₀ g) (add_zero n) := by
  let := Ext.quotientSourceModule I N n
  let := Ext.quotientSourceModule I N' n
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [Ext.quotientSourceModule_mk_smul, Ext.smul_comp]

omit [HasExt.{w} (ModuleCat.{u} R)] in
-- Source multiplication is independent of the existence and size of Ext groups.
example (r : R) :
    Ext.quotientSourceMul I (Ideal.Quotient.mk I r) =
      r • 𝟙 (ModuleCat.of R (R ⧸ I)) := Ext.quotientSourceMul_mk I r

-- The improper ideal is allowed without extra hypotheses.
example (e : Ext (ModuleCat.of R (R ⧸ (⊤ : Ideal R))) N n) :
    letI := Ext.quotientSourceModule (⊤ : Ideal R) N n
    Ideal.Quotient.mk (⊤ : Ideal R) (1 : R) • e = (1 : R) • e :=
  Ext.quotientSourceModule_mk_smul (⊤ : Ideal R) N n 1 e
