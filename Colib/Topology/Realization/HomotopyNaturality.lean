/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.HomotopyBridge

/-! # Actual naturality of realized simplicial homotopies

A strict square of original cylinder maps gives the corresponding
pointwise equality for the entire original realization homotopies.
The proof uses the proved inverse-cylinder naturality, rather than choosing
new homotopies with the same endpoints.


Implementation provenance:
`Quillen/Topology/Realization/HomotopyNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory MonoidalCategory
open scoped Simplicial Topology
universe u
namespace SSet

/-- Realization retains every point of a strict original cylinder square. -/
theorem realizationSimplicialHomotopy_naturality
    {X X' Y Y' : SSet.{u}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (a : X' ⟶ X) (b : Y ⟶ Y') (hs : a ▷ Δ[1] ≫ H.h ≫ b = H'.h)
    (t : unitInterval) (x : |X'|) :
    SSet.toTop.map b (realizationSimplicialHomotopy H (t, SSet.toTop.map a x)) =
      realizationSimplicialHomotopy H' (t, x) := by
  let p := (realizationCylinderIso X').inv (x, ULift.up t)
  have hn := ConcreteCategory.congr_hom (realizationCylinderIso_inv_naturality a) (x, ULift.up t)
  change SSet.toTop.map (a ▷ Δ[1]) p =
    (realizationCylinderIso X).inv (SSet.toTop.map a x, ULift.up t) at hn
  change SSet.toTop.map b (SSet.toTop.map H.h
    ((realizationCylinderIso X).inv (SSet.toTop.map a x, ULift.up t))) = SSet.toTop.map H'.h p
  rw [← hn]
  change (SSet.toTop.map (a ▷ Δ[1]) ≫ SSet.toTop.map H.h ≫ SSet.toTop.map b) p = _
  rw [← Functor.map_comp, ← Functor.map_comp, hs]

end SSet
