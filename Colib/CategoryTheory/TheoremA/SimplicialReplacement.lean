/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.Grothendieck

/-! Source: `Quillen/CategoryTheory/TheoremA/SimplicialReplacement.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd.
This is a categorical/realized resolution prerequisite, not the general Theorem A criterion. -/

/-!
# The simplicial replacement of a simplicial-set-valued diagram

This is the bisimplicial object used in the homotopy-colimit proof of
Theorem A. In bidegree `(p,q)`, its simplices consist of a chain
`d₀ ⟶ ⋯ ⟶ dₚ` and a `q`-simplex of the diagram's value at `d₀`.
The first face uses the covariant diagram map, so the variance is essential.
-/
@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The `p`th row of the simplicial replacement, itself a simplicial set. -/
def replacementRow (p : SimplexCategoryᵒᵖ) : SSet.{u} where
  obj q := Σ σ : (nerve D).obj p, (H.obj (σ.obj 0)).obj q
  map f := ↾fun x ↦ ⟨x.1, (H.obj (x.1.obj 0)).map f x.2⟩
  map_id q := by
    ext x : 3
    dsimp
    simp
  map_comp f g := by
    ext x : 3
    dsimp
    simp

/-- The initial-vertex edge selected by a simplex operator. -/
def firstVertexEdge {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    (σ : (nerve D).obj p) :
    σ.obj 0 ⟶ ((nerve D).map α σ).obj 0 :=
  σ.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0)))

/-- Changing the base chain transports the fiber simplex covariantly. -/
def replacementRowMap {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    replacementRow H p ⟶ replacementRow H q where
  app r := ↾fun x ↦ ⟨(nerve D).map α x.1, (H.map (firstVertexEdge α x.1)).app r x.2⟩
  naturality r s β := by
    ext x : 3
    dsimp [replacementRow]
    apply congrArg (Sigma.mk _)
    exact ConcreteCategory.congr_hom ((H.map (firstVertexEdge α x.1)).naturality β) x.2

@[simp]
theorem firstVertexEdge_id (p : SimplexCategoryᵒᵖ) (σ : (nerve D).obj p) :
    firstVertexEdge (𝟙 p) σ = 𝟙 (σ.obj 0) := by
  change σ.map (𝟙 (0 : Fin (p.unop.len + 1))) = _
  exact σ.map_id _

@[simp]
theorem firstVertexEdge_comp {p q r : SimplexCategoryᵒᵖ} (α : p ⟶ q) (β : q ⟶ r)
    (σ : (nerve D).obj p) :
    firstVertexEdge (α ≫ β) σ = firstVertexEdge α σ ≫
      firstVertexEdge β ((nerve D).map α σ) := by
  dsimp [firstVertexEdge, nerve]
  rw [← σ.map_comp]
  rfl

/-- The simplicial replacement as a genuine bisimplicial set. -/
def simplicialReplacement : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj p := replacementRow H p
  map α := replacementRowMap H α
  map_id p := by
    ext q x : 4
    dsimp [replacementRowMap]
    rw [firstVertexEdge_id, H.map_id]
    rfl
  map_comp α β := by
    ext q x : 4
    dsimp [replacementRowMap]
    rw [firstVertexEdge_comp, H.map_comp]
    rfl

section Naturality

variable {H} {K L : D ⥤ SSet.{u}}

/-- A map of diagrams acts on each replacement row without changing its base chain. -/
def replacementRowNatMap (η : H ⟶ K) (p : SimplexCategoryᵒᵖ) :
    replacementRow H p ⟶ replacementRow K p where
  app q := ↾fun x ↦ ⟨x.1, (η.app (x.1.obj 0)).app q x.2⟩
  naturality q r β := by
    ext x : 3
    dsimp [replacementRow]
    apply congrArg (Sigma.mk _)
    exact ConcreteCategory.congr_hom ((η.app (x.1.obj 0)).naturality β) x.2

/-- The simplicial replacement is functorial in the diagram. -/
def simplicialReplacementMap (η : H ⟶ K) :
    simplicialReplacement H ⟶ simplicialReplacement K where
  app p := replacementRowNatMap η p
  naturality p q α := by
    ext r x : 4
    dsimp [simplicialReplacement, replacementRowMap, replacementRowNatMap]
    apply congrArg (Sigma.mk _)
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (η.naturality (firstVertexEdge α x.1)) r) x.2

@[simp]
theorem simplicialReplacementMap_id :
    simplicialReplacementMap (𝟙 H) = 𝟙 (simplicialReplacement H) := rfl

@[simp]
theorem simplicialReplacementMap_comp (η : H ⟶ K) (θ : K ⟶ L) :
    simplicialReplacementMap (η ≫ θ) =
      simplicialReplacementMap η ≫ simplicialReplacementMap θ := rfl

end Naturality

/-- The simplicial replacement as a functor on diagrams. -/
def simplicialReplacementFunctor :
    (D ⥤ SSet.{u}) ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u}) where
  obj H := simplicialReplacement H
  map η := simplicialReplacementMap η

/-- In the Theorem A application, the diagram value is the nerve of `(F ↓ d)`. -/
def commaNerveDiagram {C : Type u} [SmallCategory C] (F : C ⥤ D) : D ⥤ SSet.{u} :=
  commaDiagram F ⋙ nerveFunctor

end CategoryTheory.TheoremA
