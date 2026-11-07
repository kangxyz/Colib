/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FilteredHomology
public import Colib.Topology.LocalCoefficients.TriangleHomology

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TriangleHomology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining original transition maps.

 # Original filtered transitions as genuine homology triangle maps -/

@[expose] public section
noncomputable section
open CategoryTheory Limits
open scoped Simplicial
universe u
namespace FundamentalGroupoid.LocalCoefficients

/-- The canonical filtered homology transition is the original triangle map. -/
theorem filteredHomologyDiagram_map_triangle {J : Type u} [SmallCategory J]
    (F : J ⥤ SSet.{u}) (c : Cocone F) (A : System.{u, u} |c.pt|) (n : ℕ)
    {j k : J} (a : j ⟶ k) :
    (filteredHomologyDiagram F c A n).map a =
      triangleHomologyMap (SSet.toTop.map (F.map a)).hom
        (SSet.toTop.map (c.ι.app j)).hom (SSet.toTop.map (c.ι.app k)).hom
        (stage_triangle F c j k a) A n :=
  (triangleHomologyMap_eq _ _ _ _ _ _).symm

end FundamentalGroupoid.LocalCoefficients
