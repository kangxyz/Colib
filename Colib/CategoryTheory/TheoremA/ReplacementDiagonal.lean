/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SimplicialReplacement
public import Colib.AlgebraicTopology.SimplicialSet.Diagonal

/-! Source: Quillen/CategoryTheory/TheoremA/Diagonal.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The five native SSet diagonal
helpers are reused rather than redefined. Only the replacement application is retained. -/

/-!
# The diagonal simplicial replacement and its canonical comparison maps

This constructs the usual simplicial homotopy-colimit object as the diagonal
of the replacement. No invariance theorem about its realization is built into
the definition.
-/
@[expose] public section

noncomputable section

open CategoryTheory Opposite SSet
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The Bousfield–Kan simplicial replacement model for the homotopy colimit. -/
def replacementDiagonal : SSet.{u} := diagonalSSet (simplicialReplacement H)

/-- The canonical projection to the nerve of the indexing category. -/
def replacementBaseMap : replacementDiagonal H ⟶ nerve D where
  app p := ↾fun x ↦ x.1
  naturality p q α := by
    ext x : 3
    rfl

section Comma

variable {C : Type u} [SmallCategory C] (F : C ⥤ D)

/-- A simplex of the diagonal comma replacement gives a chain of resolution
objects. The bridge arrow at `i` is `F(cᵢ) ⟶ d₀ ⟶ dᵢ`. -/
def commaDiagonalChain (p : SimplexCategoryᵒᵖ)
    (x : Σ σ : ComposableArrows D p.unop.len,
      ComposableArrows (CostructuredArrow F (σ.obj 0)) p.unop.len) :
    ComposableArrows (Resolution F) p.unop.len where
  obj i := ⟨(x.2.obj i).left, x.1.obj i,
    (x.2.obj i).hom ≫ x.1.map (homOfLE (Fin.zero_le i))⟩
  map {i j} f :=
    { left := (x.2.map f).left
      right := x.1.map f
      w := by
        dsimp
        rw [CostructuredArrow.w_assoc]
        rw [Category.assoc, ← x.1.map_comp]
        rfl }
  map_id i := by
    apply Comma.hom_ext
    · exact congrArg (fun k : x.2.obj i ⟶ x.2.obj i ↦ k.left) (x.2.map_id i)
    · simp
  map_comp f g := by
    apply Comma.hom_ext
    · change (x.2.map (f ≫ g)).left = (x.2.map f ≫ x.2.map g).left
      rw [x.2.map_comp]
    · simp

/-- The canonical simplicial map from the diagonal comma replacement to the
nerve of the comma resolution. -/
def commaDiagonalToResolution :
    replacementDiagonal (commaNerveDiagram F) ⟶ nerve (Resolution F) where
  app p := ↾fun x ↦ commaDiagonalChain F p x
  naturality p q α := by
    ext x : 3
    change commaDiagonalChain F q
      ⟨(SimplexCategory.toCat.map α.unop).toFunctor ⋙ x.1,
        (SimplexCategory.toCat.map α.unop).toFunctor ⋙ x.2 ⋙
          CostructuredArrow.map (firstVertexEdge α x.1)⟩ =
      (SimplexCategory.toCat.map α.unop).toFunctor ⋙ commaDiagonalChain F p x
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
    · dsimp [commaDiagonalChain, firstVertexEdge]
      congr 1
      rw [Category.assoc, ← x.1.map_comp]
      rfl
    · intro i j f
      apply Comma.hom_ext <;> simp [commaDiagonalChain]

/-- Its projection to `D` is the canonical projection of the homotopy-colimit model. -/
theorem commaDiagonalToResolution_target :
    commaDiagonalToResolution F ≫ nerveMap (targetProjection F) =
      replacementBaseMap (commaNerveDiagram F) := by
  ext p x : 4
  rfl

end Comma

end CategoryTheory.TheoremA
