/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.Ext.Regular
public import Colib.RingTheory.Koszul.Ext

/-!
# Ext concentration for a principal regular quotient

For a scalar regular on both the ring and the coefficient module, native Ext
from the principal ideal quotient vanishes outside degree one. Degree-zero
vanishing needs only coefficient regularity; higher-degree vanishing needs
only ring regularity. No nonunit, Noetherianity or finiteness condition is used.

Adapted from `Aglib.Algebra.Homology.Koszul.Single.Ext.Ideal` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The higher-degree calculation uses the
already migrated bounds from Stacks' native Koszul resolution. No source scalar
quotient model, one-element complex, or degree-one class is reconstructed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace Koszul

variable {R : Type u} [CommRing R]

/-- The quotient by a scalar regular on the ring has projective dimension at most one. -/
theorem principalQuotient_hasProjectiveDimensionLE (a : R) (ha : IsSMulRegular R a) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.span {a})) 1 := by
  have hs : RingTheory.Sequence.IsWeaklyRegular R [a] := by
    simpa only [RingTheory.Sequence.isWeaklyRegular_cons_iff,
      RingTheory.Sequence.IsWeaklyRegular.nil, and_true] using ha
  have h := quotient_hasProjectiveDimensionLE_of_weaklyRegular [a] hs
  rw [Ideal.ofList_singleton] at h
  exact h

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- Coefficient regularity alone kills degree-zero Ext from the principal quotient. -/
theorem principalExtZero_eq_zero_of_regular (a : R) (N : ModuleCat.{u} R)
    (hN : IsSMulRegular N a)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 0) : e = 0 :=
  e.eq_zero_of_mem_annihilator_of_isSMulRegular
    (by rw [Ideal.annihilator_quotient]; exact Ideal.subset_span (Set.mem_singleton a)) hN

/-- Ring regularity kills every Ext class above degree one, for arbitrary coefficients. -/
theorem principalExt_eq_zero_above_one (a : R) (ha : IsSMulRegular R a)
    (N : ModuleCat.{u} R) (n : ℕ) (hn : 1 < n)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N n) : e = 0 := by
  let := principalQuotient_hasProjectiveDimensionLE a ha
  exact e.eq_zero_of_hasProjectiveDimensionLT 2 (by omega)

/-- Regularity on ring and coefficients concentrates principal-quotient Ext in degree one. -/
theorem principalExt_eq_zero_of_ne_one (a : R) (ha : IsSMulRegular R a)
    (N : ModuleCat.{u} R) (hN : IsSMulRegular N a) (n : ℕ) (hn : n ≠ 1)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N n) : e = 0 := by
  cases n with
  | zero => exact principalExtZero_eq_zero_of_regular a N hN e
  | succ n => exact principalExt_eq_zero_above_one a ha N (n + 1) (by omega) e

end Koszul

attribute [colib_tag "COL-0041"] Koszul.principalQuotient_hasProjectiveDimensionLE
  Koszul.principalExtZero_eq_zero_of_regular Koszul.principalExt_eq_zero_above_one
  Koszul.principalExt_eq_zero_of_ne_one

add_to_stacks 062F
  "Ingredient: a regular singleton gives the native Koszul resolution of its ideal quotient"
  Koszul.principalQuotient_hasProjectiveDimensionLE
add_to_stacks 0CXC
  "Ingredient: a length-one projective resolution bounds projective dimension"
  Koszul.principalQuotient_hasProjectiveDimensionLE
add_to_stacks 0CXC
  "Ingredient only: finite projective resolution bound, yielding the higher Ext vanishing here"
  Koszul.principalExt_eq_zero_above_one
add_to_stacks 062F
  "Resolution ingredient only; coefficient regularity separately supplies degree-zero vanishing"
  Koszul.principalExt_eq_zero_of_ne_one
