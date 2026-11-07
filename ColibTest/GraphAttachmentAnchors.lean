/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Realization.GraphAttachmentAnchors

/-!
# Boundary endpoints and graph anchors regression tests

These test the actual chart/vertex identifications and supplied edge compatibility.
They assert anchor existence only, not generation by edges. No discrete topology
is assumed for the parameter or vertex space.
-/

open CategoryTheory CategoryTheory.Limits Convexity.StdSimplex Topology
open scoped Topology unitInterval

universe u v w

noncomputable section

example (b : boundary 1) :
    b.1 = Convexity.StdSimplex.single 0 ∨ b.1 = Convexity.StdSimplex.single 1 :=
  simplexBoundary_one_cases b

example : boundaryZero.1 = Convexity.StdSimplex.single 0 := rfl

example : boundaryOne.1 = Convexity.StdSimplex.single 1 := rfl

example : boundaryZero ≠ boundaryOne := boundaryZero_ne_one

example (b : boundary 1) : b = boundaryZero ∨ b = boundaryOne :=
  boundary_eq_zero_or_one b

namespace TopCat.GraphAttachment

variable (X : TopCat.{u}) {V D Y : TopCat.{u}}
  {f : TopCat.of (X × boundary 1) ⟶ V}
  {g : TopCat.of (X × Convexity.StdSimplex ℝ (Fin 2)) ⟶ D} {j : V ⟶ D}
  (sq : IsPushout (parameterizedSimplexBoundaryInclusion X 1) f g j)
  (h : C(D, Y)) {A : Type v} [Groupoid.{w} A]
  (F : A ⥤ FundamentalGroupoid Y) (vertex : V → A)
  (ε : ∀ c : V, F.obj (vertex c) ≅ FundamentalGroupoid.mk (h (j c)))

example (a : X) (b : boundary 1) : vertexIso X sq h F vertex ε a b =
    ε (f (a, b)) ≪≫ eqToIso (congrArg FundamentalGroupoid.mk
      (congrArg h (ConcreteCategory.congr_hom sq.w (a, b)).symm)) := rfl

example (a : X) (x : Convexity.StdSimplex ℝ (Fin 2)) : spoke X sq h F vertex ε a x =
    (vertexIso X sq h F vertex ε a boundaryZero).hom ≫
      ⟦(PathConnectedSpace.somePath (Convexity.StdSimplex.single 0) x).map
        (h.comp (simplexAttachmentCellMap X 1 (g := g) a)).continuous⟧ := rfl

example (a : X) {x y : Convexity.StdSimplex ℝ (Fin 2)} (p : Path x y) :
    spoke X sq h F vertex ε a x ≫
        (⟦p.map (h.comp (simplexAttachmentCellMap X 1 (g := g) a)).continuous⟧ :
          FundamentalGroupoid.mk (h (g (a, x))) ⟶ FundamentalGroupoid.mk (h (g (a, y)))) =
      spoke X sq h F vertex ε a y := spoke_comp X sq h F vertex ε a p

example (a : X) : spoke X sq h F vertex ε a (Convexity.StdSimplex.single 0) =
    (vertexIso X sq h F vertex ε a boundaryZero).hom := spoke_source X sq h F vertex ε a

variable (edge : ∀ a : X, vertex (f (a, boundaryZero)) ⟶ vertex (f (a, boundaryOne)))
  (hedge : ∀ a : X, spoke X sq h F vertex ε a (Convexity.StdSimplex.single 1) =
    F.map (edge a) ≫ (vertexIso X sq h F vertex ε a boundaryOne).hom)

example (z : D) : Nonempty (Anchor X sq h F vertex ε z) :=
  anchor_nonempty X sq h F vertex ε edge hedge z

example (z : D) (α : Anchor X sq h F vertex ε z) (c : V) (hc : j c = z) :
    ∃ q : α.obj ⟶ vertex c, α.hom = F.map q ≫ (ε c).hom ≫
      eqToHom (congrArg FundamentalGroupoid.mk (congrArg h hc)) := α.old c hc

example (z : D) (α : Anchor X sq h F vertex ε z) (a : X)
    (x : Convexity.StdSimplex ℝ (Fin 2)) (hx : g (a, x) = z) :
    ∃ q : α.obj ⟶ vertex (f (a, boundaryZero)),
      α.hom = F.map q ≫ spoke X sq h F vertex ε a x ≫
        eqToHom (congrArg FundamentalGroupoid.mk (congrArg h hx)) := α.cell a x hx

end TopCat.GraphAttachment
