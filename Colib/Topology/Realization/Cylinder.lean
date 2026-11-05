/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.CompactOpen
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Topological cylinders preserve colimits

Product on the right with a locally compact space has the compact-open mapping-space functor
as right adjoint. In particular, product with the topological unit interval preserves
existing colimits. This does not assert that geometric realization preserves general
products.

## Implementation provenance

Adapted from `Quillen/Topology/Realization/Cylinder.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The selected declarations retain the source
constructions and mathematical universe parameters. Namespace and dependency ownership
are changed to the underlying Mathlib objects.
-/
@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology

universe u w v

namespace TopCat

/-- The compact-open mapping-space functor for a fixed topological space. -/
def topologicalMappingSpace (K : TopCat.{u}) : TopCat.{u} ⥤ TopCat.{u} where
  obj Y := TopCat.of C(K, Y)
  map f := TopCat.ofHom ⟨ContinuousMap.comp f.hom, ContinuousMap.continuous_postcomp _⟩
  map_id Y := by ext g k; rfl
  map_comp f g := by ext h k; rfl

/-- Product with a locally compact space is left adjoint to its compact-open
mapping-space functor. -/
def topologicalProductMappingSpaceAdjunction (K : TopCat.{u}) [LocallyCompactSpace K] :
    tensorRight K ⊣ topologicalMappingSpace K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun f ↦ TopCat.ofHom f.hom.curry
          invFun := fun f ↦ TopCat.ofHom f.hom.uncurry
          left_inv := fun f ↦ by ext z; rfl
          right_inv := fun f ↦ by ext x k; rfl }
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; rfl }

/-- Topological cylinder formation preserves arbitrary existing colimits. -/
instance topologicalCylinder_preservesColimits :
    PreservesColimitsOfSize.{v, w} (tensorRight TopCat.I.{u}) := by
  let := (topologicalProductMappingSpaceAdjunction TopCat.I.{u}).isLeftAdjoint
  infer_instance

end TopCat

attribute [colib_tag "COL-0063",
  colib_ref "MunkresTopology" "Theorems 46.10-46.11, pages 286-287" "background"
    "Compact-open exponential law; the book assumes Hausdorff, unlike this Mathlib interface"]
  TopCat.topologicalMappingSpace
  TopCat.topologicalProductMappingSpaceAdjunction

attribute [colib_tag "COL-0063",
  stacks 0038 "(1), left-adjoint preservation applied to product with the topological interval"]
  TopCat.topologicalCylinder_preservesColimits
