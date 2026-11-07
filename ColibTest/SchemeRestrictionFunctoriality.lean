/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.Restriction

/-! Regression tests for actual geometric restriction and its canonical K/G functoriality. -/

universe u

open CategoryTheory CategoryTheory.ExactCategory

noncomputable section

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Tests

-- The categorical comparisons retain the native module components without Noetherian premises.
example (X : Scheme.{u}) (M : X.Vect) :
    ((Modules.vectorBundleRestrictId X).hom.app M).hom =
      (Modules.restrictFunctorId (X := X)).hom.app M.obj := rfl

example (X : Scheme.{u}) (M : SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((Modules.coherentRestrictId X).inv.app M).hom =
      (Modules.restrictFunctorId (X := X)).inv.app M.obj := rfl

example {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (M : X.Vect) :
    ((Modules.vectorBundleRestrictComp i j).hom.app M).hom =
      (Modules.restrictFunctorComp i j).hom.app M.obj := rfl

example {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (M : SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((Modules.coherentRestrictComp i j).inv.app M).hom =
      (Modules.restrictFunctorComp i j).inv.app M.obj := rfl

-- Identity and composition are strict homomorphism equalities, at the original upper universe.
example (X : Scheme.{u}) (n : ℕ) :
    restrictK (𝟙 X) n = MonoidHom.id
      (ExactStructure.SmallK.{u + 1} (Modules.vectorBundleExactStructure X) n) :=
  restrictK_id X n

example {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    restrictK (i ≫ j) n = (restrictK i n).comp (restrictK j n) :=
  restrictK_comp i j n

example {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (x : K X 0) :
    restrictK (i ≫ j) 0 x = restrictK i 0 (restrictK j 0 x) :=
  restrictK_comp_apply i j 0 x

example (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    restrictG (𝟙 X) n = MonoidHom.id
      (ExactStructure.SmallK.{u + 1} (Modules.coherentExactStructure X) n) :=
  restrictG_id X n

example {V U X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    restrictG (i ≫ j) n = (restrictG i n).comp (restrictG j n) :=
  restrictG_comp i j n

example {V U X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (x : G X 0) :
    restrictG (i ≫ j) 0 x = restrictG i 0 (restrictG j 0 x) :=
  restrictG_comp_apply i j 0 x

end AlgebraicGeometry.Scheme.Tests
