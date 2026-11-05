/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Colib.RingTheory.Koszul.TopExtCoefficients

/-! Regression tests for positive-length top Ext with arbitrary coefficients. -/

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

example (f : Fin 2 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R) (x : N) :
    Koszul.seqTopExtQuotientLinearEquiv f hf N (Submodule.Quotient.mk x) =
      Koszul.seqTopExtClass f hf N x :=
  Koszul.seqTopExtQuotientLinearEquiv_apply_mk f hf N x

example (f : Fin 2 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R) (x : N) :
    Koszul.seqTopExtClass f hf N x = 0 ↔ x ∈ Ideal.span (Set.range f) • (⊤ : Submodule R N) := by
  change x ∈ LinearMap.ker (Koszul.seqTopExtClass f hf N) ↔ _
  rw [Koszul.seqTopExtClass_ker]

example {n : ℕ} (f : Fin (n + 1) → R) (hf : Koszul.IsKoszulRegular f)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N')
    (x : N ⧸ ((Ideal.span (Set.range f)) • (⊤ : Submodule R N))) :
    (Koszul.seqTopExtQuotientLinearEquiv.{u,w} f hf N x).comp
        (Ext.mk₀ g) (add_zero (n + 1)) =
      Koszul.seqTopExtQuotientLinearEquiv.{u,w} f hf N'
        ((((Ideal.span (Set.range f)) • (⊤ : Submodule R N)).mapQ
          ((Ideal.span (Set.range f)) • (⊤ : Submodule R N')) g.hom
          (Submodule.smul_top_le_comap_smul_top (Ideal.span (Set.range f)) g.hom)) x) :=
  Koszul.seqTopExtQuotientLinearEquiv_naturality f hf g x

example {n : ℕ} (f : Fin (n + 1) → R) (hf : Koszul.IsKoszulRegular f)
    (N : ModuleCat.{u} R) (r : R ⧸ Ideal.span (Set.range f))
    (x : N ⧸ ((Ideal.span (Set.range f)) • (⊤ : Submodule R N))) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.span (Set.range f)) N (n + 1)
    Koszul.seqTopExtQuotientLinearEquiv.{u,w} f hf N (r • x) =
      r • Koszul.seqTopExtQuotientLinearEquiv.{u,w} f hf N x := by
  let := Ext.quotientSourceModule.{u,w} (Ideal.span (Set.range f)) N (n + 1)
  exact (Koszul.seqTopExtQuotientLinearEquiv.{u,w} f hf N).map_smul r x

example (f : Fin 1 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R) (x : N) :
    Koszul.seqTopExtQuotientLinearEquiv.{u,w} f hf N (Submodule.Quotient.mk x) =
      Koszul.seqTopExtClass f hf N x :=
  Koszul.seqTopExtQuotientLinearEquiv_apply_mk f hf N x
