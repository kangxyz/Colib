/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Inflations
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.Subdivision.Basic
public import Mathlib.CategoryTheory.Widesubcategory

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionTotal.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The actual total extension category

Grayson's total category is modeled by subdivision of admissible inflations.
Thus morphisms shrink the kernel and enlarge the middle object. This stage
constructs the category and its middle-object projection; the quotient-object
projection to the original Q category requires a separate construction.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [Limits.HasFiniteBiproducts C] (E : ExactStructure C)

/-- The total extension category, in Grayson's subdivision model. -/
abbrev ExtensionTotal := CategoryTheory.Subdivision E.InflationCategory

/-- An original admissible monomorphism as a total extension object. -/
def extensionTotalOf {A B : C} (i : A ⟶ B) (hi : E.inflation i) : E.ExtensionTotal :=
  Subdivision.of (A := (⟨A⟩ : E.InflationCategory))
    (B := (⟨B⟩ : E.InflationCategory)) ⟨i, hi⟩

/-- Retain the actual middle object of an extension. -/
def extensionTotalMiddle : E.ExtensionTotal ⥤ C :=
  Subdivision.codomain ⋙ wideSubcategoryInclusion E.inflation

/-- A genuine quotient presentation for a total extension object. -/
structure ExtensionQuotientData (x : E.ExtensionTotal) where
  /-- The quotient object. -/
  obj : C
  /-- The quotient map from the middle object. -/
  π : x.base.obj ⟶ obj
  /-- The kernel inclusion is annihilated. -/
  zero : x.fiber.unop.hom.hom ≫ π = 0
  /-- The quotient belongs to the original exact structure. -/
  conflation : E.conflation (ShortComplex.mk x.fiber.unop.hom.hom π zero)

/-- Recover the quotient from the actual inflation axiom, without extra exactness data. -/
def extensionQuotientData (x : E.ExtensionTotal) : E.ExtensionQuotientData x := by
  apply Classical.choice
  obtain ⟨Q, p, h, hc⟩ := x.fiber.unop.hom.property
  exact ⟨⟨Q, p, h, hc⟩⟩

/-- Recovered quotient presentations have the categorical cokernel universal property. -/
def ExtensionQuotientData.isColimit {x : E.ExtensionTotal}
    (q : E.ExtensionQuotientData x) : IsColimit (CokernelCofork.ofπ q.π q.zero) :=
  E.cokernel _ q.conflation

/-- Quotient choices are canonically isomorphic by their actual universal properties. -/
def ExtensionQuotientData.iso {x : E.ExtensionTotal}
    (q r : E.ExtensionQuotientData x) : q.obj ≅ r.obj :=
  (q.isColimit E).coconePointUniqueUpToIso (r.isColimit E)

/-- The canonical quotient isomorphism preserves the quotient map. -/
@[reassoc (attr := simp)]
theorem ExtensionQuotientData.π_iso_hom {x : E.ExtensionTotal}
    (q r : E.ExtensionQuotientData x) : q.π ≫ (q.iso E r).hom = r.π :=
  (q.isColimit E).comp_coconePointUniqueUpToIso_hom (r.isColimit E) WalkingParallelPair.one

end CategoryTheory.ExactCategory.ExactStructure
