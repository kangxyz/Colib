/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import StacksFrontier.Examples.Algebra.FGModulesModuloTorsion

/-!
# The actual exact fraction-field functor on finite modules

For a commutative Noetherian domain, the native Stacks fraction-field functor
is additive and exact, and its kernel is precisely the finitely generated torsion
modules. Its existing localization theorem therefore applies at its actual kernel.
All constructions use `FGModuleCat` and the original scalar-localization functor.

## Implementation provenance

This is the fraction-field specialization of the categorical input to
`Quillen/GTheory/FiniteModules/LocalizationSequence.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The localization input is the native
Stacks theorem, Tag 0B0L. Arbitrary multiplicative-set localization is not asserted.
-/
@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Small.{v, u} R]

instance fractionModuleFunctor_additive :
    (Stacks.Examples.fgFractionModuleFunctor.{u, v} R).Additive := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let : F.Additive := ⟨by intros; rfl⟩
  dsimp [Stacks.Examples.fgFractionModuleFunctor]
  infer_instance

instance fractionModuleFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (Stacks.Examples.fgFractionModuleFunctor.{u, v} R) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits _
    (Stacks.Examples.fgTorsionModuleProperty R)

instance fractionModuleFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (Stacks.Examples.fgFractionModuleFunctor.{u, v} R) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits _
    (Stacks.Examples.fgTorsionModuleProperty R)

/-- The kernel is exactly the native elementwise nonzerodivisor-torsion property. -/
theorem fractionModuleFunctor_kernel :
    (Stacks.Examples.fgFractionModuleFunctor.{u, v} R).kernel =
      Stacks.Examples.fgTorsionModuleProperty R := by
  funext M
  exact propext (ObjectProperty.SerreClassLocalization.isZero_obj_iff _ _ M)

/-- The original native scalar-localization functor, with its proved exactness. -/
def fractionExactFunctor :
    ExactFunctor (abelianExactStructure (FGModuleCat.{v} R))
      (abelianExactStructure (FGModuleCat.{v} (FractionRing R))) where
  toFunctor := Stacks.Examples.fgFractionModuleFunctor R
  map_conflation _ hS := hS.map_of_exact _

@[simp]
theorem fractionExactFunctor_toFunctor :
    (fractionExactFunctor.{u, v} R).toFunctor =
      Stacks.Examples.fgFractionModuleFunctor R := rfl

instance fractionExactFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (fractionExactFunctor.{u, v} R).toFunctor :=
  fractionModuleFunctor_preservesFiniteLimits R

instance fractionExactFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (fractionExactFunctor.{u, v} R).toFunctor :=
  fractionModuleFunctor_preservesFiniteColimits R

instance fractionExactFunctor_isLocalization :
    (fractionExactFunctor.{u, v} R).toFunctor.IsLocalization
      (fractionExactFunctor R).toFunctor.kernel.isoModSerre := by
  change (Stacks.Examples.fgFractionModuleFunctor R).IsLocalization
    (Stacks.Examples.fgFractionModuleFunctor R).kernel.isoModSerre
  have hW : (Stacks.Examples.fgFractionModuleFunctor.{u, v} R).kernel.isoModSerre =
      (Stacks.Examples.fgTorsionModuleProperty R).isoModSerre := by
    ext M N f
    simp only [ObjectProperty.isoModSerre_iff, fractionModuleFunctor_kernel]
  rw [hW]
  infer_instance

end FGModuleCat

attribute [stacks 0B0L "the original fraction-field functor and its torsion kernel"]
  FGModuleCat.fractionModuleFunctor_kernel
  FGModuleCat.fractionExactFunctor
