/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionProjection
public import Colib.CategoryTheory.ExactCategory.QIsomorphisms
/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionIdentityQuotient.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Canonical zero quotients of identity extensions -/
@[expose] public section

open CategoryTheory.ExactCategory


open CategoryTheory CategoryTheory.Limits ZeroObject
noncomputable section
universe u v
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)
/-- The chosen quotient of an identity inflation is canonically the original zero object. -/
def identityQuotientIsoZero (A : C) :
    E.extensionProjectionObject (E.extensionTotalOf (𝟙 A) (E.inflation.id_mem A)) ≅ (0 : C) := by
  let x := E.extensionTotalOf (𝟙 A) (E.inflation.id_mem A)
  exact ((E.extensionQuotientData x).isColimit E).coconePointUniqueUpToIso
    (cokernel.isColimitCoconeZeroCocone (𝟙 A))
/-- The identity extension projects to the original zero vertex of Q, up to its canonical iso. -/
def identityProjectionIsoZero (A : C) :
    E.extensionProjectionQObj (E.extensionTotalOf (𝟙 A) (E.inflation.id_mem A)) ≅
      QConstruction.of E.deflation E.inflation (0 : C) :=
  E.qIsoOfIso (E.identityQuotientIsoZero A)
end CategoryTheory.ExactCategory.ExactStructure
