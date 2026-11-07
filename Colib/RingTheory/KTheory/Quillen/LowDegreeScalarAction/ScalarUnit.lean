/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Quillen.LowDegreeScalarAction.ScalarUnit
public import Colib.Algebra.Category.ModuleCat.FiniteProjective
public import Mathlib.Algebra.Category.FGModuleCat.Abelian

/-!
# Low-degree scalar operations for finite modules and finite projectives

These are the finite-module specializations of the general scalar operation on a
linear exact category. They retain the original categories, maps and universe levels.

## Implementation provenance

Extracted from `Quillen/KTheory/LowDegreeScalarAction/ScalarUnit.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The five declarations and their bodies
are unchanged; the general construction has no finite-module dependency.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Linear
attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory.ExactCategory.ScalarUnit

section Consumers
universe r
variable (R : Type r) [CommRing R]

/-- On actual finite modules the component is the same ordinary scalar multiplication. -/
theorem finiteModule_scalarNatAut_apply (a : Rˣ) (M : FGModuleCat.{r} R) (x : M) :
    (((scalarNatAut R (FGModuleCat.{r} R) a).asIso).hom.app M).hom x = (a : R) • x := rfl

/-- On actual finite projectives the component is the same ordinary scalar multiplication. -/
theorem finiteProjective_scalarNatAut_apply (a : Rˣ)
    (M : ModuleCat.FiniteProjective.Category.{r, r} R) (x : M.obj) :
    (((scalarNatAut R (ModuleCat.FiniteProjective.Category.{r, r} R) a).asIso).hom.app M).hom x =
      (a : R) • x := rfl

/-- The original K-one scalar operation on actual finite projective modules. -/
def finiteProjectiveKOneAction : Rˣ →*
    ((ModuleCat.FiniteProjective.exactStructure.{r, r} R).K 1 →*
      (ModuleCat.FiniteProjective.exactStructure.{r, r} R).K 2) :=
  kOneAction.{r, r + 1, r} R (ModuleCat.FiniteProjective.exactStructure.{r, r} R)

variable [IsNoetherianRing R]

/-- The original K-one scalar operation on finite modules over a noetherian commutative ring. -/
def finiteModuleKOneAction : Rˣ →*
    ((abelianExactStructure (FGModuleCat.{r} R)).K 1 →*
      (abelianExactStructure (FGModuleCat.{r} R)).K 2) :=
  kOneAction.{r, r + 1, r} R (abelianExactStructure (FGModuleCat.{r} R))

/-- The K-one scalar operation on that actual upper finite-module model. -/
def upperFiniteModuleKOneAction : Rˣ →*
    ((abelianExactStructure (FGModuleCat.{r} R)).SmallK.{r + 1} 1 →*
      (abelianExactStructure (FGModuleCat.{r} R)).SmallK.{r + 1} 2) :=
  smallModelKOneAction.{r, r + 1, r, r + 1} R (abelianExactStructure (FGModuleCat.{r} R))

end Consumers

end CategoryTheory.ExactCategory.ScalarUnit
