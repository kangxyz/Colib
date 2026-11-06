/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexBoundary.SimplyConnected
public import Colib.Topology.Realization.SimplexAttachment.AnnulusBoundary

/-!
# Annulus

The constructed higher-boundary trivialization pulled back along the original
radial boundary projection of the actual higher simplex annulus.
-/

@[expose] public section

noncomputable section
open CategoryTheory Convexity.StdSimplex FundamentalGroupoid.OpenCover
universe u v
namespace Convexity.StdSimplex.Boundary
open TopCat.SimplexAttachment
variable {n : ℕ}

/-- The constructed higher-boundary trivialization pulled back along the original
radial boundary projection of the actual higher simplex annulus. -/
def annulusConstantIso {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (simplexBoundary (n + 3)) ⥤ C) :
    FundamentalGroupoid.map (annulusBoundary (n + 3)) ⋙ F ≅
      (Functor.const (FundamentalGroupoid (simplexAnnulus (n + 3)))).obj
        (F.obj (FundamentalGroupoid.mk (vertex 0))) :=
  Functor.isoWhiskerLeft (FundamentalGroupoid.map (annulusBoundary (n + 3)))
    (boundaryConstantIso F)

/-- Every actual annulus loop is killed by every radial pullback of a
higher-boundary groupoid functor, with no loop-killing premise. -/
theorem annulus_loop_eq_id {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (simplexBoundary (n + 3)) ⥤ C)
    (x : simplexAnnulus (n + 3)) (p : Path x x) :
    (FundamentalGroupoid.map (annulusBoundary (n + 3)) ⋙ F).map
        (Path.Homotopic.Quotient.mk p) =
      𝟙 (F.obj (FundamentalGroupoid.mk (annulusBoundary (n + 3) x))) :=
  boundary_loop_eq_id F _ (p.map (annulusBoundary (n + 3)).continuous)

end Convexity.StdSimplex.Boundary
