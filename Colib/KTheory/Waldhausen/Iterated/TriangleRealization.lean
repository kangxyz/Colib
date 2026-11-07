/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.TriangleStructure
public import Colib.Topology.Realization.SimplexCylinder

/-!
# Realized iterated triangles and their independent structure coordinate

The actual stage triangle is realized using the proved product-simplex homeomorphism. Its full
simplex parameter commutes with the original spectrum's separate suspension parameter.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/TriangleRealization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, simplex faces,
whole fixed-zero family, and independent structure parameters are retained under native ownership.
  -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

variable {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
  (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))

/-- The mixed simplicial coordinate square keeps the whole original triangle. -/
theorem stageTransformationTriangle_structure (r : ℕ) :
    stageCylinder r V ▷ Δ[2] ≫ stageTransformationTriangle (r + 1) η θ hη hθ =
      simplicialSimplexCylinderSwap ((stages r).obj V) 2 ≫
        stageTransformationTriangle r η θ hη hθ ▷ Δ[1] ≫ stageCylinder r W := by
  ext n z : 4
  exact stageTriangleFunction_structure r η θ hη hθ n z.1.1 z.1.2 z.2

/-- The actual continuous simplex-parameter family of original iterated-stage maps. -/
def stageTriangleRealization (r : ℕ) :
    C(stageSpace r V × |(Δ[2] : SSet.{u})|, stageSpace r W) :=
  realizationSimplexFamily (stageTransformationTriangle r η θ hη hθ)

/-- The realized triangle and original structure time remain fully independent. -/
theorem stageTriangleRealization_structure (r : ℕ)
    (z : |(Δ[2] : SSet.{u})|) (t : unitInterval) (x : stageSpace r V) :
    stageTriangleRealization η θ hη hθ (r + 1) (stageLoopMap r V x t, z) =
      stageLoopMap r W (stageTriangleRealization η θ hη hθ r (x, z)) t :=
  realizationSimplexFamily_interchange (stageTransformationTriangle r η θ hη hθ)
    (stageTransformationTriangle (r + 1) η θ hη hθ) (stageHomotopy r V) (stageHomotopy r W)
    (stageTransformationTriangle_structure η θ hη hθ r) z t x

end CategoryTheory.Waldhausen.IteratedS
