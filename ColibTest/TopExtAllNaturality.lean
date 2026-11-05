/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Colib.RingTheory.Koszul.TopExtAllNaturality

/-! All-length quotient-class naturality and scalar-action regression tests. -/

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

example (f : Fin 0 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R)
    (b : R ⧸ Ideal.span (Set.range f))
    (x : N ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R N))) :
    Koszul.seqTopExtQuotientLinearEquivAll f hf N (b • x) =
      (Ext.mk₀ (Ext.quotientSourceMul (Ideal.span (Set.range f)) b)).comp
        (Koszul.seqTopExtQuotientLinearEquivAll f hf N x) (zero_add 0) :=
  Koszul.seqTopExtQuotientLinearEquivAll_smul f hf N b x

example {n : ℕ} (f : Fin n → R) (hf : Koszul.IsKoszulRegular f)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') (x : N) :
    (Koszul.seqTopExtQuotientLinearEquivAll f hf N (Submodule.Quotient.mk x)).comp
      (Ext.mk₀ g) (add_zero n) =
        Koszul.seqTopExtQuotientLinearEquivAll f hf N' (Submodule.Quotient.mk (g x)) := by
  exact Koszul.seqTopExtQuotientLinearEquivAll_naturality f hf g (Submodule.Quotient.mk x)

example {n : ℕ} (f : Fin n → R) (hf : Koszul.IsKoszulRegular f)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N')
    (x : N ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R N))) :
    (Koszul.seqTopExtQuotientLinearEquivAll f hf N x).comp (Ext.mk₀ g) (add_zero n) =
      Koszul.seqTopExtQuotientLinearEquivAll f hf N'
        (((Ideal.span (Set.range f) • (⊤ : Submodule R N)).mapQ
          (Ideal.span (Set.range f) • (⊤ : Submodule R N')) g.hom
          (Submodule.smul_top_le_comap_smul_top (Ideal.span (Set.range f)) g.hom)) x) :=
  Koszul.seqTopExtQuotientLinearEquivAll_naturality f hf g x

example {n : ℕ} (f : Fin n → R) (hf : Koszul.IsKoszulRegular f)
    (N : ModuleCat.{u} R) (r : R)
    (x : N ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R N))) :
    Koszul.seqTopExtQuotientLinearEquivAll f hf N
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) r • x) =
      (Koszul.seqTopExtQuotientLinearEquivAll f hf N x).comp
        (Ext.mk₀ (r • 𝟙 N)) (add_zero n) :=
  Koszul.seqTopExtQuotientLinearEquivAll_mk_smul f hf N r x
