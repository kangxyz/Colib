/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Core

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/Extensions/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Fibers of the extension construction

An extension over `X` is represented by an admissible epimorphism onto `X`.
Only isomorphisms over `X` are retained. The omitted kernel exists by the
exact-structure axioms; its inclusion will be recovered separately. This file
constructs the actual zero fiber equivalence. It does not identify a strict
fiber with a comma category or assume any Theorem B transition condition.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- Admissible epimorphisms with fixed codomain. -/
def extensionProperty (X : C) : ObjectProperty (Over X) := fun p => E.deflation p.hom

/-- The category before restricting its arrows to isomorphisms. -/
abbrev ExtensionOver (X : C) := (E.extensionProperty X).FullSubcategory

/-- The groupoid of extensions with fixed quotient, represented by their deflations. -/
abbrev ExtensionFiber (X : C) := Core (E.ExtensionOver X)

/-- An actual kernel presentation of an admissible epimorphism. -/
structure ExtensionKernelData {X : C} (p : E.ExtensionOver X) where
  /-- The kernel object. -/
  obj : C
  /-- The kernel inclusion. -/
  ι : obj ⟶ p.obj.left
  /-- The composite with the deflation vanishes. -/
  zero : ι ≫ p.obj.hom = 0
  /-- This is a conflation of the original exact structure. -/
  conflation : E.conflation (ShortComplex.mk ι p.obj.hom zero)

/-- Recover kernel data from admissibility, with no additional splitting assumption. -/
def extensionKernelData {X : C} (p : E.ExtensionOver X) : E.ExtensionKernelData p := by
  apply Classical.choice
  obtain ⟨K, i, h, hc⟩ := p.property
  exact ⟨⟨K, i, h, hc⟩⟩

/-- Every recovered kernel satisfies the genuine categorical universal property. -/
def ExtensionKernelData.isLimit {X : C} {p : E.ExtensionOver X}
    (k : E.ExtensionKernelData p) : IsLimit (KernelFork.ofι k.ι k.zero) :=
  E.kernel _ k.conflation

/-- Different choices of kernel presentation are canonically isomorphic. -/
def ExtensionKernelData.iso {X : C} {p : E.ExtensionOver X}
    (k l : E.ExtensionKernelData p) : k.obj ≅ l.obj :=
  (k.isLimit E).conePointUniqueUpToIso (l.isLimit E)

/-- The canonical kernel isomorphism preserves the inclusion. -/
@[reassoc (attr := simp)]
theorem ExtensionKernelData.iso_hom_ι {X : C} {p : E.ExtensionOver X}
    (k l : E.ExtensionKernelData p) : (k.iso E l).hom ≫ l.ι = k.ι :=
  (k.isLimit E).conePointUniqueUpToIso_hom_comp (l.isLimit E) WalkingParallelPair.zero

/-- Forget the extension's deflation, retaining its middle object. -/
def extensionMiddle (X : C) : E.ExtensionOver X ⥤ C :=
  (E.extensionProperty X).ι ⋙ Over.forget X

/-- Compose the quotient map with an admissible epimorphism. This is the
contravariant extension transport for the reversed-deflation leg of a Q span. -/
def extensionPostcompose {X Y : C} (f : X ⟶ Y) (hf : E.deflation f) :
    E.ExtensionOver X ⥤ E.ExtensionOver Y where
  obj p := ⟨Over.mk (p.obj.hom ≫ f), E.deflation_comp _ _ p.property hf⟩
  map {p q} g := ObjectProperty.homMk (Over.homMk g.hom.left (by
    change g.hom.left ≫ (q.obj.hom ≫ f) = p.obj.hom ≫ f
    simpa only [Category.assoc] using congrArg (fun k => k ≫ f) (Over.w g.hom)))

/-- The same quotient transport on the actual extension groupoids. -/
def extensionFiberPostcompose {X Y : C} (f : X ⟶ Y) (hf : E.deflation f) :
    E.ExtensionFiber X ⥤ E.ExtensionFiber Y :=
  (E.extensionPostcompose f hf).core

/-- Every object determines the extension onto zero. -/
def extensionToZero : C ⥤ E.ExtensionOver (0 : C) where
  obj X := ⟨Over.mk (0 : X ⟶ 0), E.deflation_zero X⟩
  map f := ObjectProperty.homMk (Over.homMk f (by simp))

/-- The category of admissible epimorphisms onto zero is the original category. -/
def extensionOverZeroEquivalence : E.ExtensionOver (0 : C) ≌ C where
  functor := E.extensionMiddle 0
  inverse := E.extensionToZero
  unitIso := NatIso.ofComponents (fun p =>
    (E.extensionProperty 0).isoMk
      (Over.isoMk (Iso.refl _) (by exact (isZero_zero C).eq_of_tgt _ _)))
    (by intro X Y f; apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext;
        change f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.left; simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by intro X Y f; change f ≫ 𝟙 _ = 𝟙 _ ≫ f; simp)
  functor_unitIso_comp X := by change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp

/-- The zero fiber in Grayson's extension construction is the isomorphism groupoid. -/
def extensionFiberZeroEquivalence : E.ExtensionFiber (0 : C) ≌ Core C :=
  E.extensionOverZeroEquivalence.core

end CategoryTheory.ExactCategory.ExactStructure
