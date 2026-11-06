/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.ReplacementDiagonal
public import Mathlib.CategoryTheory.Limits.Shapes.End

/-! Source: Quillen/CategoryTheory/TheoremA/Coend.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universal properties retained. -/

/-!
# The diagonal as a coend

For a bisimplicial set `X`, its diagonal is the coend of
`(p,q) ↦ Xₚ × Δ[q]`. This is a genuine universal property, proved simplexwise,
and is the algebraic part of the diagonal/iterated-realization comparison.
-/
@[expose] public section

noncomputable section

open SSet CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})

/-- The bifunctor whose coend is the diagonal. -/
def diagonalCoendBifunctor : SimplexCategoryᵒᵖ ⥤ SimplexCategory ⥤ SSet.{u} where
  obj p := SSet.stdSimplex ⋙ tensorLeft (X.obj p)
  map α :=
    { app n := X.map α ▷ SSet.stdSimplex.obj n
      naturality n m f := by simp [whisker_exchange] }
  map_id p := by ext n; simp
  map_comp α β := by ext n; simp

/-- Evaluation of a row against the representing simplex. -/
def diagonalEvaluation (n : SimplexCategory) :
    X.obj (op n) ⊗ SSet.stdSimplex.obj n ⟶ diagonalSSet X where
  app p := ↾fun x ↦ (X.map x.2.down.op).app p x.1
  naturality p q α := by
    ext x : 3
    change (X.map ((α.unop ≫ x.2.down).op)).app q ((X.obj (op n)).map α x.1) =
      (X.obj q).map α ((X.map α).app p ((X.map x.2.down.op).app p x.1))
    rw [op_comp, X.map_comp]
    change (X.map α).app q ((X.map x.2.down.op).app q ((X.obj (op n)).map α x.1)) = _
    rw [← NatTrans.naturality_apply, NatTrans.naturality_apply]

/-- Evaluation is natural in the bisimplicial set. -/
theorem diagonalEvaluation_naturality {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (η : X ⟶ Y) (n : SimplexCategory) :
    (η.app (op n) ▷ SSet.stdSimplex.obj n) ≫ diagonalEvaluation Y n =
      diagonalEvaluation X n ≫ diagonalMap η := by
  ext q x : 4
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (η.naturality x.2.down.op) q) x.1).symm

/-- Evaluation is dinatural in the simplex index. -/
theorem diagonalEvaluation_condition {n m : SimplexCategory} (f : n ⟶ m) :
    (X.map f.op ▷ SSet.stdSimplex.obj n) ≫ diagonalEvaluation X n =
      (X.obj (op m) ◁ SSet.stdSimplex.map f) ≫ diagonalEvaluation X m := by
  ext q x : 4
  change (X.map x.2.down.op).app q ((X.map f.op).app q x.1) =
    (X.map (x.2.down ≫ f).op).app q x.1
  rw [op_comp, X.map_comp]
  rfl

/-- The diagonal, equipped with all its canonical row evaluation maps. -/
def diagonalCowedge : Cowedge (diagonalCoendBifunctor X) :=
  Cowedge.mk (diagonalSSet X) (diagonalEvaluation X)
    (fun {_ _} f ↦ diagonalEvaluation_condition X f)

/-- A cowedge is evaluated on the identity simplex to give a map out of the diagonal. -/
def diagonalCowedgeDesc (s : Cowedge (diagonalCoendBifunctor X)) :
    diagonalSSet X ⟶ s.pt where
  app p := ↾fun x ↦ (s.π p.unop).app p (x, ULift.up (𝟙 p.unop))
  naturality p q α := by
    ext x : 3
    have h := congrArg
      (fun k : X.obj p ⊗ SSet.stdSimplex.obj q.unop ⟶ s.pt ↦
        k.app q ((X.obj p).map α x, ULift.up (𝟙 q.unop)))
      (Cowedge.condition s α.unop)
    have h' := congrArg
      (fun k : (X.obj p ⊗ SSet.stdSimplex.obj p.unop).obj p ⟶ s.pt.obj q ↦
        k (x, ULift.up (𝟙 p.unop))) ((s.π p.unop).naturality α)
    dsimp [diagonalCoendBifunctor] at h
    change (s.π q.unop).app q
      ((X.obj q).map α ((X.map α).app p x), ULift.up (𝟙 q.unop)) = _
    rw [← NatTrans.naturality_apply]
    have hstd : (SSet.stdSimplex.map α.unop).app q (ULift.up (𝟙 q.unop)) =
        (SSet.stdSimplex.obj p.unop).map α (ULift.up (𝟙 p.unop)) := by
      change ULift.up (𝟙 q.unop ≫ α.unop) = ULift.up (α.unop ≫ 𝟙 p.unop)
      simp
    change (s.π q.unop).app q
      ((X.map α).app q ((X.obj p).map α x), ULift.up (𝟙 q.unop)) = _ at h
    change (s.π p.unop).app q
      ((X.obj p).map α x, (SSet.stdSimplex.obj p.unop).map α (ULift.up (𝟙 p.unop))) = _ at h'
    exact h.trans (by rw [hstd]; exact h')

/-- The universal map has the required restriction to each row. -/
theorem diagonalEvaluation_desc (s : Cowedge (diagonalCoendBifunctor X))
    (n : SimplexCategory) :
    diagonalEvaluation X n ≫ diagonalCowedgeDesc X s = s.π n := by
  ext p x : 4
  have h := congrArg
    (fun k : X.obj (op n) ⊗ SSet.stdSimplex.obj p.unop ⟶ s.pt ↦
      k.app p (x.1, ULift.up (𝟙 p.unop)))
    (Cowedge.condition s x.2.down)
  have hstd : (SSet.stdSimplex.map x.2.down).app p (ULift.up (𝟙 p.unop)) = x.2 := by
    change ULift.up (𝟙 p.unop ≫ x.2.down) = x.2
    rw [Category.id_comp]
    rfl
  change (s.π p.unop).app p
    ((X.map x.2.down.op).app p x.1, ULift.up (𝟙 p.unop)) =
      (s.π n).app p (x.1, (SSet.stdSimplex.map x.2.down).app p (ULift.up (𝟙 p.unop))) at h
  rw [hstd] at h
  exact h

/-- Evaluation exhibits the diagonal as an actual coend. -/
def diagonalCowedgeIsColimit : IsColimit (diagonalCowedge X) :=
  Multicofork.IsColimit.mk _ (diagonalCowedgeDesc X)
    (diagonalEvaluation_desc X) (by
      intro s m hm
      ext p x : 4
      have h := congrArg
        (fun k : X.obj p ⊗ SSet.stdSimplex.obj p.unop ⟶ s.pt ↦
          k.app p (x, ULift.up (𝟙 p.unop))) (hm p.unop)
      change m.app p ((X.map (𝟙 p)).app p x) =
        (s.π p.unop).app p (x, ULift.up (𝟙 p.unop)) at h
      rw [X.map_id] at h
      exact h)

end CategoryTheory.TheoremA
