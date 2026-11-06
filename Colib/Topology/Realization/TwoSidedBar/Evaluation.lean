/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.TwoSidedBar.Basic
public import Colib.CategoryTheory.TheoremA.Augmentations

/-!
# Evaluation augmentation of the two-sided bar

Evaluation gives the augmentation maps and their naturality for the two-sided bar construction.


Implementation provenance:
`Quillen/Topology/Realization/TwoSidedBar/Evaluation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA



noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u

namespace SSet.TwoSidedBar
open TheoremA

/-- An honest small indexing category in the coefficient universe. -/
abbrev Index := AsSmall.{u} SimplexCategoryᵒᵖ

/-- The original ordinal of the explicit universe-raised index. -/
abbrev indexProjection : Index.{u} ⥤ SimplexCategoryᵒᵖ := AsSmall.down

/-- The actual diagram pulled back only along the universe adapter. -/
abbrev liftedDiagram (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : Index.{u} ⥤ SSet.{u} :=
  indexProjection ⋙ H

/-- The two-sided bar for an arbitrary actual bisimplicial set. -/
abbrev bar (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  object indexProjection (liftedDiagram H)

/-- The complete initial-to-final edge in an indexing chain. -/
def fullEdge {p : SimplexCategoryᵒᵖ} (s : (nerve Index.{u}).obj p) :
    s.obj 0 ⟶ s.obj (Fin.last p.unop.len) :=
  s.map (homOfLE (Fin.zero_le _))

/-- An outer restriction breaks the full edge into its first, middle and
last pieces, all as actual indexing-category arrows. -/
theorem fullEdge_reindex {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    (s : (nerve Index.{u}).obj p) :
    firstVertexEdge α s ≫ fullEdge ((nerve Index.{u}).map α s) ≫ lastVertexEdge α s = fullEdge s
      := by
  dsimp [firstVertexEdge, fullEdge, lastVertexEdge, nerve]
  rw [← s.map_comp, ← s.map_comp]
  rfl

variable (H : SimplexCategoryᵒᵖ ⥤ SSet.{u})

/-- Evaluation at one outer degree, with its original inner simplicial degree. -/
def evaluationRow (p : SimplexCategoryᵒᵖ) :
    (bar H).obj p ⟶ diagonalSSet H where
  app q := ↾fun z ↦
    (H.map (indexProjection.map (fullEdge z.1) ≫ z.2.2.down.op)).app q z.2.1
  naturality q r β := by
    ext z : 3
    let f := indexProjection.map (fullEdge z.1) ≫ z.2.2.down.op
    change (H.map (f ≫ β)).app r ((H.obj (indexProjection.obj (z.1.obj 0))).map β z.2.1) =
      (H.obj r).map β ((H.map β).app q ((H.map f).app q z.2.1))
    have h := ConcreteCategory.congr_hom ((H.map (f ≫ β)).naturality β) z.2.1
    simpa only [H.map_comp, NatTrans.comp_app, types_comp_apply] using h

/-- The genuine second augmentation evaluates in the unchanged diagonal. -/
def evaluation : bar H ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (diagonalSSet H) where
  app p := evaluationRow H p
  naturality p q α := by
    ext r z : 4
    change (H.map (indexProjection.map (fullEdge ((nerve Index).map α z.1)) ≫
        indexProjection.map (lastVertexEdge α z.1) ≫ z.2.2.down.op)).app r
        ((H.map (indexProjection.map (firstVertexEdge α z.1))).app r z.2.1) =
      (H.map (indexProjection.map (fullEdge z.1) ≫ z.2.2.down.op)).app r z.2.1
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← H.map_comp]
    apply congrArg (fun f ↦ (H.map f).app r z.2.1)
    have h := congrArg (fun f ↦ indexProjection.map f ≫ z.2.2.down.op)
      (fullEdge_reindex α z.1)
    simpa only [Functor.map_comp, Category.assoc] using h

/-- Evaluation keeps the original diagonal and is strictly natural in H. -/
theorem evaluation_naturality {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J) :
    map indexProjection (Functor.whiskerLeft indexProjection η) ≫ evaluation J =
      evaluation H ≫ (Functor.const SimplexCategoryᵒᵖ).map (diagonalMap η) := by
  ext p q z : 5
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (η.naturality (indexProjection.map (fullEdge z.1) ≫ z.2.2.down.op)) q)
      z.2.1 |>.symm

end SSet.TwoSidedBar

end
