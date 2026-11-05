/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.PrincipalGeneratorChange

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

example (a c : R) (r : R) :
    ModuleCat.principalQuotientMulMap a c (Ideal.Quotient.mk (Ideal.span {c * a}) r) =
      Ideal.Quotient.mk (Ideal.span {a}) r := rfl

example (a c : R) (ha : IsSMulRegular R a) (hca : IsSMulRegular R (c * a)) (x : R) :
    (Ext.mk₀ (ModuleCat.principalQuotientMulMap a c)).comp
      (Koszul.principalExtOneClass a ha (ModuleCat.of R R) x) (zero_add 1) =
        Koszul.principalExtOneClass (c * a) hca (ModuleCat.of R R) (c * x) :=
  Koszul.principalExtOneClass_generatorChange a c ha hca (ModuleCat.of R R) x

example (a c : R) (ha : IsSMulRegular R a) (hca : IsSMulRegular R (c * a))
    (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ (ModuleCat.principalQuotientMulMap a c)).comp
      (Koszul.principalExtOneClass a ha N x) (zero_add 1) =
        Koszul.principalExtOneClass (c * a) hca N (c • x) :=
  Koszul.principalExtOneClass_generatorChange a c ha hca N x
