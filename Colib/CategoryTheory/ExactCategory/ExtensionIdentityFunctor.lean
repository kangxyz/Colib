/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionIdentityQuotient
public import Colib.CategoryTheory.ExactCategory.Isomorphisms
public import Colib.CategoryTheory.Subdivision.Action
public import Mathlib.CategoryTheory.Core
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionFunctor
public import Colib.CategoryTheory.QConstruction.ZeroEndomorphisms
public import Colib.CategoryTheory.FiberedCategory.IsoFiber.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionIdentityFunctor.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Identity extensions and the zero fiber

An isomorphism acts on an identity extension by its inverse on the kernel
coordinate and itself on the middle coordinate. Its chosen quotient is related
to zero by the existing canonical cokernel isomorphism, without identifying
the chosen quotient definitionally with zero.
-/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The identity inflation associated to an original object. -/
abbrev identityExtension (A : C) : E.ExtensionTotal :=
  E.extensionTotalOf (𝟙 A) (E.inflation.id_mem A)

/-- The original isomorphism groupoid enters the identity extensions. -/
def identityExtensionFunctor : Core C ⥤ E.ExtensionTotal where
  obj A := E.identityExtension A.of
  map f := Subdivision.homMk
    (⟨f.iso.inv, E.inflation_of_iso f.iso.symm⟩)
    (⟨f.iso.hom, E.inflation_of_iso f.iso⟩) (by
      apply WideSubcategory.hom_ext
      change f.iso.inv ≫ 𝟙 _ ≫ f.iso.hom = 𝟙 _
      simp)
  map_id A := by
    apply Subdivision.hom_ext
    · simp only [Subdivision.homMk_domainMap, Subdivision.domainMap_id]
      apply WideSubcategory.hom_ext
      rfl
    · apply WideSubcategory.hom_ext
      rfl
  map_comp f g := by
    apply Subdivision.hom_ext
    · simp only [Subdivision.homMk_domainMap, Subdivision.domainMap_comp]
      apply WideSubcategory.hom_ext
      rfl
    · apply WideSubcategory.hom_ext
      rfl

@[simp]
lemma identityExtensionFunctor_map_base {A B : Core C} (f : A ⟶ B) :
    ((E.identityExtensionFunctor.map f).base).hom = f.iso.hom := rfl

@[simp]
lemma identityExtensionFunctor_map_domain {A B : Core C} (f : A ⟶ B) :
    (Subdivision.domainMap (E.identityExtensionFunctor.map f)).hom = f.iso.inv := rfl

/-- A morphism between identity extensions recovers an original isomorphism. -/
def identityExtensionPreimage {A B : Core C}
    (f : E.identityExtensionFunctor.obj A ⟶ E.identityExtensionFunctor.obj B) : A ⟶ B := by
  let k : A.of ⟶ B.of := f.base.hom
  let h : B.of ⟶ A.of := (Subdivision.domainMap f).hom
  have hhk : h ≫ k = 𝟙 B.of := by
    have hw := congrArg (fun g ↦ g.hom) (Subdivision.factorization f)
    change h ≫ 𝟙 A.of ≫ k = 𝟙 B.of at hw
    simpa using hw
  let : Mono k := E.mono_of_inflation f.base.property
  exact ⟨⟨k, h, (cancel_mono k).1 (by simp [Category.assoc, hhk]), hhk⟩⟩

instance identityExtensionFunctor_faithful : E.identityExtensionFunctor.Faithful where
  map_injective {_ _} _ _ h := Core.hom_ext (congrArg (fun k ↦ k.base.hom) h)

instance identityExtensionFunctor_full : E.identityExtensionFunctor.Full where
  map_surjective f := by
    refine ⟨E.identityExtensionPreimage f, ?_⟩
    apply Subdivision.hom_ext
    · apply WideSubcategory.hom_ext
      rfl
    · apply WideSubcategory.hom_ext
      rfl

/-- The objectwise zero comparison uses the canonical chosen-quotient isomorphism. -/
def identityExtensionZeroIso (A : Core C) :
    E.extensionProjectionQObj (E.identityExtensionFunctor.obj A) ≅
      QConstruction.of E.deflation E.inflation (0 : C) :=
  E.identityProjectionIsoZero A.of

/-- The canonical chosen-quotient comparisons are natural, since every map
into the original zero Q-vertex is unique when it exists. -/
def identityExtensionProjectionIsoZero :
    E.identityExtensionFunctor ⋙ E.extensionProjection ≅
      (Functor.const (Core C)).obj E.qZero :=
  NatIso.ofComponents (fun A ↦ E.identityExtensionZeroIso A) (fun _ ↦
    (E.qHom_subsingleton_of_isZero _ _ (isZero_zero C)).elim _ _)

/-- Identity extensions enter the actual zero isomorphism fiber. -/
def identityExtensionIsoFiber : Core C ⥤ IsoFiber E.extensionProjection E.qZero :=
  IsoFiber.lift E.extensionProjection E.qZero E.identityExtensionFunctor
    E.identityExtensionProjectionIsoZero.symm

end CategoryTheory.ExactCategory.ExactStructure
