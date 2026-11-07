/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Subcategory
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundles
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Extension
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf

/-!
# The inherited exact structure on vector bundles

The category is the native `Scheme.Vect`, with its native finite locally free predicate.
Its conflations are exactly those short complexes whose underlying module sheaves form a
short exact sequence. Extension closure, zero objects and invariance under isomorphism are
supplied by the pinned Stacks results.

Implementation provenance: the exact-category construction of
`Aglib/AlgebraicGeometry/Modules/LocallyFree/Exact.lean` at
`2c34f185fa859e862661f939cd216b07bcccfb26`, used by
`Quillen/AlgebraicGeometry/Scheme/VectorBundle/KTheory.lean` at `c561118b`.
The earlier local-freeness category is replaced by the existing native `Scheme.Vect`;
no additional category or alternate sheaf model is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- The standard exact structure on all module sheaves on a scheme. -/
def sheafExactStructure : ExactStructure X.Modules := abelianExactStructure X.Modules

instance finiteLocallyFree_containsZero :
    ObjectProperty.ContainsZero
      (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) where
  exists_zero := ⟨0, isZero_zero _,
    Stacks.Perfect.BoundedLocallyFreeComplexes.finiteLocallyFree_of_isZero X 0
      (isZero_zero _)⟩

instance finiteLocallyFree_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) where
  of_iso e h := by
    have := h
    exact SheafOfModules.IsFiniteLocallyFree.of_iso e

instance finiteLocallyFree_isExtensionClosed :
    (sheafExactStructure X).IsExtensionClosed
      (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) where
  prop_middle {S} hS h₁ h₃ :=
    Stacks.FiniteLocallyFree.isFiniteLocallyFree_of_shortExact S hS h₁ h₃

instance finiteLocallyFree_isClosedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :=
  (sheafExactStructure X).extensionClosed_finiteProducts _

/-- The exact structure on the native category of vector bundles, inherited from module
sheaves. It uses all ambient short exact sequences, not only globally split sequences. -/
def vectorBundleExactStructure : ExactStructure X.Vect :=
  ExactSubcategory.exactStructure (sheafExactStructure X)
    (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)

/-- A vector-bundle conflation is precisely an ambient short exact sequence. -/
@[simp]
theorem vectorBundleExactStructure_conflation (S : ShortComplex X.Vect) :
    (vectorBundleExactStructure X).conflation S ↔
      (S.map (ObjectProperty.ι
        (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M))).ShortExact :=
  Iff.rfl

/-- The literal full inclusion of vector bundles into module sheaves is exact. -/
def vectorBundleExactInclusion :
    ExactFunctor (vectorBundleExactStructure X) (sheafExactStructure X) :=
  ExactSubcategory.exactInclusion (sheafExactStructure X)
    (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)

@[simp]
theorem vectorBundleExactInclusion_obj (M : X.Vect) :
    (vectorBundleExactInclusion X).toFunctor.obj M = M.obj := rfl

@[simp]
theorem vectorBundleExactInclusion_map {M N : X.Vect} (f : M ⟶ N) :
    (vectorBundleExactInclusion X).toFunctor.map f = f.hom := rfl

end AlgebraicGeometry.Scheme.Modules
