/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.HomotopyNaturality

/-!
# Strict squares of the original realized homotopies

The actual simplicial cylinder square preserves every point of the original
realization homotopies, in the covariant square orientation.
-/
/-! Implementation source: `Quillen/Topology/Realization/HomotopySquare.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual cylinder isomorphisms,
simultaneous interval coordinates and both projection maps are unchanged. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open scoped Simplicial Topology
universe u v
namespace SSet

theorem realizationSimplicialHomotopy_square
    {X X' Y Y' : SSet.{u}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (a : X ⟶ X') (b : Y ⟶ Y') (hs : H.h ≫ b = a ▷ Δ[1] ≫ H'.h)
    (t : unitInterval) (x : |X|) :
    SSet.toTop.map b (realizationSimplicialHomotopy H (t, x)) =
      realizationSimplicialHomotopy H' (t, SSet.toTop.map a x) := by
  let p := (realizationCylinderIso X).inv (x, ULift.up t)
  have hn := ConcreteCategory.congr_hom (realizationCylinderIso_inv_naturality a) (x, ULift.up t)
  change SSet.toTop.map (a ▷ Δ[1]) p =
    (realizationCylinderIso X').inv (SSet.toTop.map a x, ULift.up t) at hn
  change SSet.toTop.map b (SSet.toTop.map H.h p) = SSet.toTop.map H'.h
    ((realizationCylinderIso X').inv (SSet.toTop.map a x, ULift.up t))
  rw [← hn]
  change (SSet.toTop.map H.h ≫ SSet.toTop.map b) p =
    (SSet.toTop.map (a ▷ Δ[1]) ≫ SSet.toTop.map H'.h) p
  rw [← Functor.map_comp, ← Functor.map_comp, hs]

end SSet
