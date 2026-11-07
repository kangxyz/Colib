/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.MapComposition

/-!
Adapted from `Quillen/Topology/LocalCoefficients/FilteredColimit.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual coefficient maps.

 # Genuine simplicial maps for commuting spatial triangles -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A spatial triangle induces a map with its pullback coefficient identification. -/
def triangleSimplicialMap {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, Z))
    (w : s = t.comp h) (A : System.{u, u} Z) :
    simplicialModule (pullback s A) ⟶ simplicialModule (pullback t A) :=
  coefficientSimplicialMap (eqToHom (congrArg (fun f ↦ pullback f A) w)) ≫
    coefficientSimplicialMap (pullbackCompositionIso h t A).hom ≫
      pushforwardSimplicialMap h (pullback t A)

theorem triangleSimplicialMap_inclusion {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, Z))
    (w : s = t.comp h) (A : System.{u, u} Z) (n : SimplexCategory)
    (σ : SingularSimplex X n) :
    chainInclusion (pullback s A) σ ≫ (triangleSimplicialMap h s t w A).app (Opposite.op n) =
      eqToHom (congrArg (fun f : C(X, Z) ↦ fiber A (f (σ (Convexity.StdSimplex.single 0)))) w) ≫
        chainInclusion (pullback t A) (h.comp σ) := by
  subst s
  simp [triangleSimplicialMap, coefficientSimplicialMap, pushforwardSimplicialMap,
    pullbackCompositionIso]

end FundamentalGroupoid.LocalCoefficients
