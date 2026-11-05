/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Ext vanishing at a zero term of a projective resolution

An actual zero term of a supplied native projective resolution kills the
corresponding native Ext group. The Koszul projective resolution supplied by
Stacks is the immediate consumer. No enough-projectives assumption is needed.

Adapted from `Aglib.CategoryTheory.Abelian.Projective.Dimension` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, retaining the original proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v w

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasExt.{w} C] {X : C} (P : ProjectiveResolution X)

/-- A zero term of the original supplied resolution kills every native Ext
class in that same degree, for arbitrary coefficient objects and Ext universes. -/
theorem ext_eq_zero_of_isZero_X {Y : C} (n : ℕ)
    (hn : IsZero (P.complex.X n)) (e : Ext X Y n) : e = 0 := by
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 1) rfl
  have hzero : f = 0 := hn.eq_of_src _ _
  subst f
  exact P.extMk_zero (n + 1) rfl

end CategoryTheory.ProjectiveResolution
