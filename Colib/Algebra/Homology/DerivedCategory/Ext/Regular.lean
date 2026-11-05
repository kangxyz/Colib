/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Regular.LinearMap

/-!
# Degree-zero Ext from an annihilated module to a regular module

A scalar annihilating the source and acting injectively on the target kills
all degree-zero Ext classes. This uses Mathlib's existing vanishing criterion
for linear maps and the native degree-zero Ext equivalence.

Extracted from the degree-zero argument of
`Aglib.Algebra.Homology.Koszul.Single.Ext` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Unlike that cyclic-source argument,
the result applies to any annihilated source module and keeps an independent
module universe. No Noetherianity or finiteness is assumed.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Abelian.Ext

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{v} R)]

/-- A source-annihilating scalar that is regular on the target kills degree-zero Ext. -/
theorem eq_zero_of_mem_annihilator_of_isSMulRegular
    {X Y : ModuleCat.{v} R} {a : R} (hX : a ∈ Module.annihilator R X)
    (hY : IsSMulRegular Y a) (e : Ext X Y 0) : e = 0 := by
  let := hY.linearMap_subsingleton_of_mem_annihilator hX
  have : Subsingleton (Ext X Y 0) :=
    (Ext.homEquiv₀.trans ModuleCat.homEquiv).subsingleton
  exact Subsingleton.elim _ _

end CategoryTheory.Abelian.Ext
