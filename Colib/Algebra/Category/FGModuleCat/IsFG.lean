/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic

/-!
# Isomorphism invariance of finite generation

This equips Mathlib's existing finite-module property with its native
isomorphism-closure instance, using the underlying linear equivalence.
-/
@[expose] public section

universe u v
open CategoryTheory

/-- Finite generation is invariant under the native module-category isomorphisms. -/
instance ModuleCat.isFG_isClosedUnderIsomorphisms (R : Type u) [Ring R] :
    (ModuleCat.isFG.{v} R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e h := by
    let : Module.Finite R X := h
    exact Module.Finite.equiv e.toLinearEquiv
