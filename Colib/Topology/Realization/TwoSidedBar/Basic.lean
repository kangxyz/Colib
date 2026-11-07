/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Coproduct
public import Colib.Topology.Homotopy.Equiv.Sigma
public import Colib.AlgebraicTopology.SimplicialSet.Diagonal
public import Colib.CategoryTheory.TheoremA.ReplacementDiagonal
public import Mathlib.CategoryTheory.Category.ULift

/-!
# The two-sided bar construction

The two-sided bar diagram and its diagonal, row and column objects retain their literal
    categorical and topological models.


Implementation provenance:
`Quillen/Topology/Realization/TwoSidedBar/Basic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA



noncomputable section
open Topology TopCat SSet
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.TwoSidedBar
open TheoremA
variable {D : Type u} [SmallCategory D]
variable (L : D ⥤ SimplexCategoryᵒᵖ) (H : D ⥤ SSet.{u})

/-- The bar's actual inner simplicial row. -/
def row (p : SimplexCategoryᵒᵖ) : SSet.{u} :=
  SSet.simplicialSigma fun s : (nerve D).obj p ↦
    H.obj (s.obj 0) ⊗ SSet.stdSimplex.obj (L.obj (s.obj (Fin.last p.unop.len))).unop

/-- The final-vertex edge has the variance opposite to the first-vertex edge. -/
def lastVertexEdge {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    (s : (nerve D).obj p) :
    ((nerve D).map α s).obj (Fin.last q.unop.len) ⟶ s.obj (Fin.last p.unop.len) :=
  s.map (homOfLE (Fin.le_last (α.unop.toOrderHom (Fin.last q.unop.len))))

@[simp] theorem lastVertexEdge_id (p : SimplexCategoryᵒᵖ) (s : (nerve D).obj p) :
    lastVertexEdge (𝟙 p) s = 𝟙 (s.obj (Fin.last p.unop.len)) := by
  change s.map (𝟙 _) = _
  exact s.map_id _

@[simp] theorem lastVertexEdge_comp {p q r : SimplexCategoryᵒᵖ}
    (α : p ⟶ q) (β : q ⟶ r) (s : (nerve D).obj p) :
    lastVertexEdge (α ≫ β) s =
      lastVertexEdge β ((nerve D).map α s) ≫ lastVertexEdge α s := by
  dsimp [lastVertexEdge, nerve]
  rw [← s.map_comp]
  rfl

/-- An outer operator transports the first coefficient forward and the
last standard-simplex coordinate backward. -/
def rowMap {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) : row L H p ⟶ row L H q where
  app r := ↾fun z ↦ ⟨(nerve D).map α z.1,
    (H.map (firstVertexEdge α z.1)).app r z.2.1,
    ULift.up (z.2.2.down ≫ (L.map (lastVertexEdge α z.1)).unop)⟩
  naturality r s β := by
    ext z : 3
    apply congrArg (Sigma.mk _)
    apply Prod.ext
    · exact ConcreteCategory.congr_hom ((H.map (firstVertexEdge α z.1)).naturality β) z.2.1
    · exact congrArg ULift.up (Category.assoc _ _ _)

/-- The two-sided bar is a genuine bisimplicial set. -/
def object : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj p := row L H p
  map α := rowMap L H α
  map_id p := by
    ext r z : 4
    dsimp [rowMap]
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply Prod.ext
    · change (H.map (firstVertexEdge (𝟙 p) z.1)).app r z.2.1 = z.2.1
      rw [firstVertexEdge_id, H.map_id]
      rfl
    · apply ULift.ext
      change z.2.2.down ≫ (L.map (lastVertexEdge (𝟙 p) z.1)).unop = z.2.2.down
      rw [lastVertexEdge_id]
      exact (congrArg (fun f ↦ z.2.2.down ≫ f.unop)
        (L.map_id (z.1.obj (Fin.last p.unop.len)))).trans (Category.comp_id _)
  map_comp α β := by
    ext r z : 4
    dsimp [rowMap]
    simp only [firstVertexEdge_comp, lastVertexEdge_comp, H.map_comp, L.map_comp,
      NatTrans.comp_app, types_comp_apply, unop_comp]
    congr 2

/-- Forgetting the standard-simplex coordinate gives the actual replacement row. -/
def dropRow (p : SimplexCategoryᵒᵖ) : row L H p ⟶ replacementRow H p where
  app _q := ↾fun z ↦ ⟨z.1, z.2.1⟩
  naturality _ _ _ := rfl

/-- The first natural augmentation is the prescribed coordinate projection. -/
def drop : object L H ⟶ simplicialReplacement H where
  app p := dropRow L H p
  naturality _ _ _ := rfl

variable {H} {J K : D ⥤ SSet.{u}}

/-- A transformation acts on the first coefficient, retaining the chain and
last simplex literally. -/
def mapRow (η : H ⟶ J) (p : SimplexCategoryᵒᵖ) : row L H p ⟶ row L J p where
  app q := ↾fun z ↦ ⟨z.1, (η.app (z.1.obj 0)).app q z.2.1, z.2.2⟩
  naturality q r α := by
    ext z : 3
    apply congrArg (Sigma.mk _)
    exact Prod.ext (ConcreteCategory.congr_hom ((η.app (z.1.obj 0)).naturality α) z.2.1) rfl

/-- The bar construction is natural in its coefficient diagram. -/
def map (η : H ⟶ J) : object L H ⟶ object L J where
  app p := mapRow L η p
  naturality p q α := by
    ext r z : 4
    apply congrArg (Sigma.mk _)
    exact Prod.ext (ConcreteCategory.congr_hom
      (NatTrans.congr_app (η.naturality (firstVertexEdge α z.1)) r) z.2.1) rfl

@[simp] theorem map_id : map L (𝟙 H) = 𝟙 (object L H) := rfl
@[simp] theorem map_comp (η : H ⟶ J) (θ : J ⟶ K) :
    map L (η ≫ θ) = map L η ≫ map L θ := rfl

/-- The drop augmentation commutes strictly with diagram transformations. -/
@[reassoc] theorem drop_naturality (η : H ⟶ J) :
    map L η ≫ drop L J = drop L H ≫ simplicialReplacementMap η := rfl

end SSet.TwoSidedBar

end
