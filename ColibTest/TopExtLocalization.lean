/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Colib.RingTheory.Koszul.TopExtLocalization

/-! Fixed-base coefficient localization in empty and positive lengths. -/

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (T : Submonoid R) {N N' : ModuleCat.{u} R} (g : N ⟶ N') [IsLocalizedModule T g.hom]

example (f : Fin 0 → R) (hf : Koszul.IsKoszulRegular f) :
    IsLocalizedModule T
      ((Ext.mk₀ g).postcompOfLinear R (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))
        (add_zero 0)) :=
  Koszul.seqTopExtPostcomp_isLocalizedModule T g f hf

example (f : Fin 2 → R) (hf : Koszul.IsKoszulRegular f) :
    IsLocalizedModule T
      ((Ext.mk₀ g).postcompOfLinear R (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))
        (add_zero 2)) :=
  Koszul.seqTopExtPostcomp_isLocalizedModule T g f hf

section GenericQuotient

open scoped Pointwise
universe v z

example {A : Type u} [CommRing A] (U : Submonoid A)
    {M : Type v} {P : Type z} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (h : M →ₗ[A] P) [IsLocalizedModule U h]
    (I : Ideal A) :
    IsLocalizedModule U ((I • (⊤ : Submodule A M)).mapQ
      (I • (⊤ : Submodule A P)) h (Submodule.smul_top_le_comap_smul_top I h)) :=
  Submodule.isLocalizedModule_mapQ_smul_top U h I

end GenericQuotient
