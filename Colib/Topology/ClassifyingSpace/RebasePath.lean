/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.PointedFunctor
public import Colib.CategoryTheory.Functor.Rebase.Composition
public import Colib.Topology.ClassifyingSpace.NaturalTransformationTracks
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup

/-! # Actual edge paths for rebased classifying-space maps

The original base-object isomorphism determines the entire rebasing track.
Its path transport identifies the raw and strictly pointed homotopy-group maps.
Adapted from `Quillen/KTheory/Map/RebasePath.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining all maps and universes.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology HomotopyGroup
open scoped unitInterval
universe u v

namespace CategoryTheory

section Rebase

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- An equality of the endpoint does not change the parametrized categorical edge. -/
theorem classifyingSpacePath_comp_eqToHom_apply {a b d : D} (f : a ⟶ b)
    (h : b = d) (t : unitInterval) :
    classifyingSpacePath (f ≫ eqToHom h) t = classifyingSpacePath f t := by
  subst d
  simp only [eqToHom_refl, Category.comp_id]

/-- The supplied base-object isomorphism, as a path from the actual image point. -/
def classifyingSpaceIsoBasePath (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    Path (classifyingSpaceMap F (classifyingSpacePoint c)) (classifyingSpacePoint d) :=
  (classifyingSpacePath e.hom).cast (classifyingSpaceMap_point F c) rfl

/-- The original natural isomorphism supplies the homotopy to the rebased map. -/
def rebaseFunctorHomotopy (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    (classifyingSpaceMap F).hom.Homotopy
      (classifyingSpaceMap (rebaseFunctor F c d e)).hom :=
  classifyingSpaceNaturalTransformationHomotopy (rebaseFunctorIso F c d e).hom

/-- The whole rebasing track is the original supplied edge, including its parametrization. -/
theorem rebaseFunctorHomotopy_base_track (F : C ⥤ D) (c : C) (d : D)
    (e : F.obj c ≅ d) :
    ((rebaseFunctorHomotopy F c d e).evalAt (classifyingSpacePoint c)).cast rfl
      (rebaseFunctor_map_point F c d e).symm = classifyingSpaceIsoBasePath F c d e := by
  ext t
  change classifyingSpaceNaturalTransformationHomotopy (rebaseFunctorIso F c d e).hom
    (t, classifyingSpacePoint c) = classifyingSpacePath e.hom t
  rw [classifyingSpaceNaturalTransformationHomotopy_vertex_general,
    rebaseFunctorIso_hom_base]
  exact classifyingSpacePath_comp_eqToHom_apply e.hom _ t

/-- Moving the basepoint along the original rebasing track identifies the actual maps
in every finite homotopy degree, including degree zero. -/
theorem pathTransport_rebaseFunctor_homotopyGroupMap (F : C ⥤ D) (c : C) (d : D)
    (e : F.obj c ≅ d) (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace C) (classifyingSpacePoint c)) :
    pathTransport (classifyingSpaceIsoBasePath F c d e) n
      (HomotopyGroup.map (classifyingSpaceMap F).hom rfl a) =
        HomotopyGroup.map (classifyingSpaceMap (rebaseFunctor F c d e)).hom
          (rebaseFunctor_map_point F c d e) a := by
  rw [← rebaseFunctorHomotopy_base_track F c d e]
  exact pathTransport_homotopyGroupMap_homotopy_cast
    (rebaseFunctorHomotopy F c d e) (classifyingSpacePoint c) rfl
    (rebaseFunctor_map_point F c d e) n a

/-- The existing strictly pointed map is the original raw map corrected by the actual
supplied isomorphism edge. -/
theorem pointedShiftedHomotopyGroupMap_eq_pathTransport (F : C ⥤ D) (c : C) (d : D)
    (e : F.obj c ≅ d) (n : ℕ) :
    pointedShiftedHomotopyGroupMap F c d e n =
      (pathTransportMulEquiv (classifyingSpaceIsoBasePath F c d e) n).toMonoidHom.comp
        (piMap n (classifyingSpaceMap F).hom rfl) := by
  apply MonoidHom.ext
  intro a
  exact (pathTransport_rebaseFunctor_homotopyGroupMap F c d e (n + 1) a).symm

end Rebase

end CategoryTheory
