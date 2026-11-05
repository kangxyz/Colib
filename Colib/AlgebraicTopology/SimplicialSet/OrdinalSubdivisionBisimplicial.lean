/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.OrdinalSubdivision
public import Colib.AlgebraicTopology.SimplicialSet.Diagonal


/-! # Subdivision in either direction of a bisimplicial set

Actual horizontal and vertical endpoint maps and their diagonal identities.
No realization equivalence is assumed or proved here.
-/
/-! Implementation provenance: extracted from
`Quillen/Topology/Realization/OrdinalSubdivisionBisimplicial.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, proofs,
assumptions, and universes are retained; only namespaces/imports are migrated.
-/
@[expose] public section


noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.OrdinalSubdivision
open SSet

/-- Subdivision in the outer simplicial direction only. -/
def horizontal (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  δ.op ⋙ X

/-- Subdivision in the inner simplicial direction only. -/
def vertical (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  X ⋙ subdivisionFunctor

/-- Restrict the outer direction to the first half. -/
def horizontalEndpoint (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : horizontal X ⟶ X where
  app p := X.map (first.app p.unop).op
  naturality p q f := by
    change X.map (δ.map f.unop).op ≫ X.map (first.app q.unop).op =
      X.map (first.app p.unop).op ≫ X.map f
    rw [← X.map_comp, ← X.map_comp]
    exact congrArg X.map (congrArg Quiver.Hom.op (first.naturality f.unop)).symm

/-- Restrict the inner direction to the first half, naturally in the outer degree. -/
def verticalEndpoint (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : vertical X ⟶ X :=
  Functor.whiskerLeft X endpointNatTrans

/-- The double subdivision diagonal is the ordinary subdivision of the diagonal. -/
def doubleDiagonalIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalSSet (horizontal (vertical X)) ≅ subdivision (diagonalSSet X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- Restricting the outer and then inner direction is the ordinary endpoint. -/
theorem horizontalEndpoint_verticalEndpoint (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalMap (horizontalEndpoint (vertical X)) ≫ diagonalMap (verticalEndpoint X) =
      (doubleDiagonalIso X).hom ≫ endpoint (diagonalSSet X) := by
  ext p z
  rfl

/-- Restricting the inner and then outer direction gives the same ordinary endpoint. -/
theorem verticalEndpoint_horizontalEndpoint (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalMap (Functor.whiskerLeft δ.op (verticalEndpoint X)) ≫
      diagonalMap (horizontalEndpoint X) =
      (doubleDiagonalIso X).hom ≫ endpoint (diagonalSSet X) := by
  ext p z
  exact ConcreteCategory.congr_hom
    ((X.map (first.app p.unop).op).naturality (first.app p.unop).op) z

end SSet.OrdinalSubdivision
