/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexBoundary.TriangleRelation
public import Colib.Topology.Realization.SimplexAttachment.AnnulusBoundary

/-!
# Annulus Loops

Pull back the constructed boundary trivialization along the actual radial
projection of the two-simplex annulus.
-/

@[expose] public section

noncomputable section
open CategoryTheory Convexity.StdSimplex FundamentalGroupoid.OpenCover
universe u v
namespace Convexity.StdSimplex.Boundary
open TopCat.SimplexAttachment

/-- Pull back the constructed boundary trivialization along the actual radial
projection of the two-simplex annulus. -/
def annulusConstantIsoOfTriangle {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (simplexBoundary 2) ⥤ C)
    (h : edgeMap F 0 1 ≫ edgeMap F 1 2 = edgeMap F 0 2) :
    FundamentalGroupoid.map (annulusBoundary 2) ⋙ F ≅
      (Functor.const (FundamentalGroupoid (simplexAnnulus 2))).obj
        (F.obj (FundamentalGroupoid.mk (vertex 0))) :=
  Functor.isoWhiskerLeft (FundamentalGroupoid.map (annulusBoundary 2))
    (boundaryConstantIsoOfTriangle F h)

/-- Every actual annulus loop is killed under the explicit original triangle
relation; the annulus itself is not claimed to be simply connected. -/
theorem annulus_loop_eq_id_of_triangle {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (simplexBoundary 2) ⥤ C)
    (h : edgeMap F 0 1 ≫ edgeMap F 1 2 = edgeMap F 0 2)
    (x : simplexAnnulus 2) (p : Path x x) :
    (FundamentalGroupoid.map (annulusBoundary 2) ⋙ F).map (Path.Homotopic.Quotient.mk p) =
      𝟙 (F.obj (FundamentalGroupoid.mk (annulusBoundary 2 x))) :=
  boundary_loop_eq_id_of_triangle F h _ (p.map (annulusBoundary 2).continuous)

end Convexity.StdSimplex.Boundary
