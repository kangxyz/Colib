/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SimplexProductCoefficients

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SimplexProductMaps.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Actual maps of parameterized simplices with local coefficients

For an arbitrary continuous map over a specified base map, the affine contraction
to the original target first vertex reduces the homology comparison to that base
map with the actual restricted coefficient system. No product decomposition of
the given local system is assumed.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual first-vertex contraction for any map over the specified base map. -/
def simplexProductMapVertexHomotopy (m n : ℕ) (f : C(X, Y))
    (g : C(X × _root_.stdSimplex ℝ (Fin (m + 1)), Y × _root_.stdSimplex ℝ (Fin (n + 1))))
    (h : (simplexProductProjection Y n).comp g = f.comp (simplexProductProjection X m)) :
    ((simplexProductVertex Y n 0).comp (f.comp (simplexProductProjection X m))).Homotopy g :=
  ((simplexProductVertexHomotopy Y n 0).compContinuousMap g).cast (by
    apply ContinuousMap.ext
    intro z
    exact congrArg (simplexProductVertex Y n 0) (congrArg (fun k ↦ k z) h)) rfl

/-- A map of parameterized simplices is a homology isomorphism exactly when its
original base map is, with coefficients restricted to the target first vertex. -/
theorem simplexProductMap_homology_isIso_iff (m n : ℕ) (f : C(X, Y))
    (g : C(X × _root_.stdSimplex ℝ (Fin (m + 1)), Y × _root_.stdSimplex ℝ (Fin (n + 1))))
    (h : (simplexProductProjection Y n).comp g = f.comp (simplexProductProjection X m))
    (A : System.{u, u} (Y × _root_.stdSimplex ℝ (Fin (n + 1)))) (k : ℕ) :
    IsIso (pushforwardHomologyMap g A k) ↔
      IsIso (pushforwardHomologyMap f (pullback (simplexProductVertex Y n 0) A) k) := by
  have := simplexProductVertex_homology_isIso Y n 0 A k
  have := simplexProductProjection_homology_isIso X m
    (pullback f (pullback (simplexProductVertex Y n 0) A)) k
  have : IsIso (coefficientHomologyMap
      (pullbackCompositionIso (f.comp (simplexProductProjection X m))
        (simplexProductVertex Y n 0) A).hom k) := by
    change IsIso (coefficientHomologyIso _ k).hom
    infer_instance
  have : IsIso (coefficientHomologyMap
      (pullbackCompositionIso (simplexProductProjection X m) f
        (pullback (simplexProductVertex Y n 0) A)).hom k) := by
    change IsIso (coefficientHomologyIso _ k).hom
    infer_instance
  rw [← isIso_pushforwardHomologyMap_iff_of_homotopy
    (simplexProductMapVertexHomotopy m n f g h) A k]
  rw [pushforwardHomologyMap_comp, isIso_comp_left_iff, isIso_comp_right_iff,
    pushforwardHomologyMap_comp, isIso_comp_left_iff, isIso_comp_left_iff]

end FundamentalGroupoid.LocalCoefficients
