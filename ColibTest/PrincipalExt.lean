/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.PrincipalExt

open CategoryTheory CategoryTheory.Abelian

universe u v w

variable {R : Type u} [CommRing R]

-- The generic degree-zero criterion retains independent module and Ext universes.
example [HasExt.{w} (ModuleCat.{v} R)] {X Y : ModuleCat.{v} R} {a : R}
    (hX : a ∈ Module.annihilator R X) (hY : IsSMulRegular Y a)
    (e : Ext X Y 0) : e = 0 :=
  e.eq_zero_of_mem_annihilator_of_isSMulRegular hX hY

-- No regularity on R is required for degree zero.
example [HasExt.{w} (ModuleCat.{u} R)] (a : R) (N : ModuleCat.{u} R)
    (hN : IsSMulRegular N a) (e : Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 0) :
    e = 0 := Koszul.principalExtZero_eq_zero_of_regular a N hN e

-- No regularity on the coefficient module is required above degree one.
example [HasExt.{w} (ModuleCat.{u} R)] (a : R) (ha : IsSMulRegular R a)
    (N : ModuleCat.{u} R) (e : Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 2) : e = 0 :=
  Koszul.principalExt_eq_zero_above_one a ha N 2 (by omega) e

example [HasExt.{w} (ModuleCat.{u} R)] (a : R) (ha : IsSMulRegular R a)
    (N : ModuleCat.{u} R) (hN : IsSMulRegular N a) (n : ℕ) (hn : n ≠ 1)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N n) : e = 0 :=
  Koszul.principalExt_eq_zero_of_ne_one a ha N hN n hn e

-- The projective-dimension bound requires no HasExt instance.
example (a : R) (ha : IsSMulRegular R a) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.span {a})) 1 :=
  Koszul.principalQuotient_hasProjectiveDimensionLE a ha

-- A unit is allowed: no proper-ideal or nonunit hypothesis is hidden in the bound.
example : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.span {(1 : R)})) 1 :=
  Koszul.principalQuotient_hasProjectiveDimensionLE 1 (IsSMulRegular.one R)

example [HasExt.{w} (ModuleCat.{u} R)] (N : ModuleCat.{u} R) (n : ℕ) (hn : n ≠ 1)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.span {(1 : R)})) N n) : e = 0 :=
  Koszul.principalExt_eq_zero_of_ne_one 1 (IsSMulRegular.one R) N
    (IsSMulRegular.one N) n hn e
