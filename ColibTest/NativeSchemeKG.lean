/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.Comparison

/-! Regression tests for native scheme exact structures, canonical K/G maps and open restriction. -/

universe u

open CategoryTheory CategoryTheory.ExactCategory

noncomputable section

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Tests

-- The native coherent exact category exists without a locally Noetherian premise.
example (X : Scheme.{u}) : ExactStructure (SheafOfModules.CoherentModules X.ringCatSheaf) :=
  Modules.coherentExactStructure X

example (X : Scheme.{u}) (n : ℕ) :
    K X n = ExactStructure.SmallK.{u + 1} (Modules.vectorBundleExactStructure X) n := rfl

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Modules.vectorBundleExactRestrict j).toFunctor = Modules.vectorBundleRestrict j := rfl

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (M : X.Vect) :
    ((Modules.vectorBundleRestrict j).obj M).obj =
      (Modules.restrictFunctor j).obj M.obj := rfl

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Vect} (f : M ⟶ N) :
    ((Modules.vectorBundleRestrict j).map f).hom = (Modules.restrictFunctor j).map f.hom := rfl

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    restrictK j n = (Modules.vectorBundleExactRestrict j).smallKMap n := rfl

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

example (n : ℕ) :
    G X n = ExactStructure.SmallK.{u + 1} (Modules.coherentExactStructure X) n := rfl

example : KToG X 0 = (Modules.vectorBundleToCoherentExact X).smallKMap 0 := rfl

example (M : X.Vect) : ((Modules.vectorBundleToCoherent X).obj M).obj = M.obj := rfl

example {M N : X.Vect} (f : M ⟶ N) :
    ((Modules.vectorBundleToCoherent X).map f).hom = f.hom := rfl

variable {X} {U : Scheme.{u}} [IsLocallyNoetherian U] (j : U ⟶ X) [IsOpenImmersion j]

example : restrictG j 0 = (Modules.coherentRestrictionExact j).smallKMap 0 := rfl

example (M : X.Vect) : ((Modules.vectorBundleToCoherentRestrictIso j).hom.app M).hom =
    𝟙 ((Modules.restrictFunctor j).obj M.obj) := rfl

example (n : ℕ) : (restrictG j n).comp (KToG X n) =
    (KToG U n).comp (restrictK j n) := KToG_restrict j n

example (n : ℕ) (x : K X n) :
    restrictG j n (KToG X n x) = KToG U n (restrictK j n x) := KToG_restrict_apply j n x

end AlgebraicGeometry.Scheme.Tests
