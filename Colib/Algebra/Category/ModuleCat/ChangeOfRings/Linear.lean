/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Base-ring linearity of native scalar extension

Adapted from `Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Linear`.
No new scalar action or extension functor is introduced.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra

universe r s m

namespace ModuleCat.Algebra

variable (R : Type r) (A : Type s) [CommRing R] [CommRing A] [Algebra R A]

/-- Native extension along an algebra map preserves base-ring scalars. -/
instance extendScalars_linear :
    (ModuleCat.extendScalars.{r,s,m} (algebraMap R A)).Linear R where
  map_smul {M N} f r := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    let := (algebraMap R A).toAlgebra
    change (1 : A) ⊗ₜ[R] (r • f m) =
      algebraMap R A r • ((1 : A) ⊗ₜ[R] f m)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    rfl

end ModuleCat.Algebra
