/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.KTheory.Quillen.Map.Functoriality
public import Colib.Topology.ClassifyingSpace.RebasePath

/-!
# Original Q-maps and strictly rebased K-maps

The natural isomorphism from a functor to its rebasing realizes to a homotopy
whose specified vertex follows exactly the edge of the supplied base-object
isomorphism. Transport along that actual edge identifies the raw induced map
with the repository's original strictly rebased homotopy-group map.

For an exact functor, the supplied Q-isomorphism is obtained from the canonical
zero-object isomorphism in the original exact category. No zero-object property
in the Q-category is used, and the definition of `CategoryTheory.ExactCategory.ExactFunctor.KMap` is
  unchanged.

Implementation provenance: `Quillen/KTheory/Map/RebasePath.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual objects, maps, degrees
and universe parameters are retained.
-/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section

open CategoryTheory CategoryTheory.Limits Topology HomotopyGroup
open scoped ZeroObject unitInterval

universe u v

namespace CategoryTheory.ExactCategory.ExactFunctor
open Topology HomotopyGroup

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The raw Q-map's actual basepoint path, obtained from the zero isomorphism before
passing to Q. -/
def qZeroBasePath (F : ExactFunctor EC ED) :
    Path (classifyingSpaceMap F.mapQ EC.kBasepoint) ED.kBasepoint :=
  classifyingSpaceIsoBasePath F.mapQ
    (QConstruction.of EC.deflation EC.inflation (0 : C))
      (QConstruction.of ED.deflation ED.inflation (0 : D))
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)

/-- The canonical path is the actual Q-arrow edge, with no change in parametrization. -/
theorem qZeroBasePath_apply (F : ExactFunctor EC ED) (t : unitInterval) :
    F.qZeroBasePath t = classifyingSpacePath
      (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom t := rfl

/-- Any displayed original-category zero isomorphism gives the same actual path.
Uniqueness is used in the original exact category, before applying `qIsoOfIso`. -/
theorem qZeroBasePath_eq_of_zeroIso (F : ExactFunctor EC ED)
    (e : F.toFunctor.obj (0 : C) ≅ (0 : D)) :
    F.qZeroBasePath = classifyingSpaceIsoBasePath F.mapQ
      (QConstruction.of EC.deflation EC.inflation (0 : C))
      (QConstruction.of ED.deflation ED.inflation (0 : D))
      (ED.qIsoOfIso e) := by
  have he : F.toFunctor.mapZeroObject = e := by
    apply Iso.ext
    apply Subsingleton.elim
  unfold qZeroBasePath
  rw [he]

/-- The raw Q-map and the normalized map are related by the original rebasing homotopy. -/
def normalizedQHomotopy (F : ExactFunctor EC ED) :
    (classifyingSpaceMap F.mapQ).hom.Homotopy (classifyingSpaceMap F.normalizedQ).hom :=
  rebaseFunctorHomotopy F.mapQ
    (QConstruction.of EC.deflation EC.inflation (0 : C))
      (QConstruction.of ED.deflation ED.inflation (0 : D))
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)

/-- Exact description of the basepoint track of the original Q-rebasing homotopy. -/
theorem normalizedQHomotopy_base_track (F : ExactFunctor EC ED) :
    ((F.normalizedQHomotopy).evalAt EC.kBasepoint).cast rfl
      (rebaseFunctor_map_point F.mapQ
        (QConstruction.of EC.deflation EC.inflation (0 : C))
      (QConstruction.of ED.deflation ED.inflation (0 : D))
        (ED.qIsoOfIso F.toFunctor.mapZeroObject)).symm = F.qZeroBasePath :=
  rebaseFunctorHomotopy_base_track F.mapQ _ _ _

/-- The original K-map equals the original raw Q-map transported along its canonical
Q-isomorphism edge. This applies to every exact functor and every K-degree. -/
theorem KMap_eq_pathTransport (F : ExactFunctor EC ED) (n : ℕ) :
    F.KMap n =
      (pathTransportMulEquiv F.qZeroBasePath n).toMonoidHom.comp
        (piMap n (classifyingSpaceMap F.mapQ).hom rfl) :=
  pointedShiftedHomotopyGroupMap_eq_pathTransport F.mapQ _ _ _ n

end CategoryTheory.ExactCategory.ExactFunctor
