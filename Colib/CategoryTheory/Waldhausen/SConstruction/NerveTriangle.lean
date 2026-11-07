/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderZero
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Actual nerve-direction triangles of composable weak transformations

The parameter sees only the nerve coordinate. Every S-row is one of the three original grids;
crossing arrows use the two given weak transformations or their genuine composite.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/NerveTriangle.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped Simplicial
universe v u v' u' v'' u''

namespace CategoryTheory.Waldhausen

/-- The triangle parameter sees only the original nerve coordinate. -/
def nerveTriangleTimeFunctor (n : SimplexCategory) {m : SimplexCategory} (τ : m ⟶ ⦋2⦌) :
    Grid₂ n m ⥤ Fin 3 :=
  (show Monotone (fun p : Grid₂ n m ↦ τ.toOrderHom p.1) from
    fun _ _ h ↦ τ.toOrderHom.monotone h.1).functor

variable {D : Type u} [Category.{v} D] {n m : SimplexCategory}
  {A B C : Grid₂ n m ⥤ D}

/-- Evaluate the actual two-arrow chain at the chosen nerve coordinate. -/
def nerveTriangleDiagram (η : A ⟶ B) (θ : B ⟶ C) (τ : m ⟶ ⦋2⦌) : Grid₂ n m ⥤ D :=
  ((nerveTriangleTimeFunctor n τ).prod' (𝟭 (Grid₂ n m))) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₂ η θ)

/-- The S-coordinate sees an unchanged row of one of the three original grids. -/
theorem nerveTriangleDiagram_rowMap (η : A ⟶ B) (θ : B ⟶ C) (τ : m ⟶ ⦋2⦌)
    (t : Fin (m.len + 1)) (i j k l : Fin (n.len + 1)) (hij : i ≤ j) (hkl : k ≤ l)
    (f : grid₂ t i j hij ⟶ grid₂ t k l hkl) :
    (nerveTriangleDiagram η θ τ).map f =
      ((ComposableArrows.mk₂ η θ).obj (τ.toOrderHom t)).map f := by
  change ((ComposableArrows.mk₂ η θ).map (𝟙 (τ.toOrderHom t))).app (grid₂ t i j hij) ≫
    ((ComposableArrows.mk₂ η θ).obj (τ.toOrderHom t)).map f = _
  rw [CategoryTheory.Functor.map_id]
  simp only [NatTrans.id_app, Category.id_comp]

private theorem selected_isSimplex₂ (W : Structure D) (η : A ⟶ B) (θ : B ⟶ C)
    (hA : IsSimplex₂ W.cof W.weq A) (hB : IsSimplex₂ W.cof W.weq B)
    (hC : IsSimplex₂ W.cof W.weq C) (a : Fin 3) :
    IsSimplex₂ W.cof W.weq ((ComposableArrows.mk₂ η θ).obj a) := by
  fin_cases a
  · exact hA
  · exact hB
  · exact hC

private theorem triangle_map_weak (W : Structure D) (η : A ⟶ B) (θ : B ⟶ C)
    {p q : Grid₂ n m} (f : p ⟶ q)
    (ha : W.weq (A.map f)) (hb : W.weq (B.map f)) (hc : W.weq (C.map f))
    (hη : W.weq (η.app p)) (hθ : W.weq (θ.app p)) (a b : Fin 3) (hab : a ≤ b) :
    W.weq (((ComposableArrows.mk₂ η θ).map (homOfLE hab)).app p ≫
      ((ComposableArrows.mk₂ η θ).obj b).map f) := by
  fin_cases a <;> fin_cases b
  · simpa using ha
  · exact W.weq.comp_mem _ _ hη hb
  · exact W.weq.comp_mem _ _ (W.weq.comp_mem _ _ hη hθ) hc
  · exact False.elim ((by decide : ¬ (1 : Fin 3) ≤ 0) hab)
  · simpa using hb
  · exact W.weq.comp_mem _ _ hθ hc
  · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 0) hab)
  · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 1) hab)
  · change W.weq (((ComposableArrows.mk₂ η θ).map (𝟙 (2 : Fin 3))).app p ≫ C.map f)
    rw [CategoryTheory.Functor.map_id]
    simpa using hc

/-- The actual triangle remains a genuine S-grid using only the original weak components. -/
theorem nerveTriangleDiagram_isSimplex₂ (W : Structure D) (η : A ⟶ B) (θ : B ⟶ C)
    (hη : ∀ p, W.weq (η.app p)) (hθ : ∀ p, W.weq (θ.app p))
    (hA : IsSimplex₂ W.cof W.weq A) (hB : IsSimplex₂ W.cof W.weq B)
    (hC : IsSimplex₂ W.cof W.weq C) (τ : m ⟶ ⦋2⦌) :
    IsSimplex₂ W.cof W.weq (nerveTriangleDiagram η θ τ) where
  zero t i := (selected_isSimplex₂ W η θ hA hB hC (τ.toOrderHom t)).zero t i
  cofibration t i j k hij hjk := by
    simp only [nerveTriangleDiagram_rowMap]
    exact (selected_isSimplex₂ W η θ hA hB hC (τ.toOrderHom t)).cofibration t i j k hij hjk
  quotient t i j k hij hjk := by
    simp only [nerveTriangleDiagram_rowMap]
    exact (selected_isSimplex₂ W η θ hA hB hC (τ.toOrderHom t)).quotient t i j k hij hjk
  weak s t i j hst hij :=
    triangle_map_weak W η θ _ (hA.weak s t i j hst hij) (hB.weak s t i j hst hij)
      (hC.weak s t i j hst hij) (hη (grid₂ s i j hij)) (hθ (grid₂ s i j hij))
      (τ.toOrderHom s) (τ.toOrderHom t) (τ.toOrderHom.monotone hst)

private theorem mk₂_whiskerLeft {K : Type u'} [Category.{v'} K]
    {K' : Type u''} [Category.{v''} K']
    (J : K' ⥤ K) {F G H : K ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) :
    ComposableArrows.mk₂ (whiskerLeft J η) (whiskerLeft J θ) =
      ComposableArrows.mk₂ η θ ⋙ (whiskeringLeft K' K D).obj J := by
  apply ComposableArrows.ext₂ (f := ComposableArrows.mk₂ (whiskerLeft J η) (whiskerLeft J θ))
    (g := ComposableArrows.mk₂ η θ ⋙ (whiskeringLeft K' K D).obj J) rfl rfl rfl <;> simp

/-- Both independent grid reindexings commute with the original triangle diagram. -/
theorem nerveTriangleDiagram_precomp (η : A ⟶ B) (θ : B ⟶ C)
    {n' m' : SimplexCategory} (α : n' ⟶ n) (β : m' ⟶ m) (τ : m ⟶ ⦋2⦌) :
    nerveTriangleDiagram (whiskerLeft (gridMap₂ α β) η)
      (whiskerLeft (gridMap₂ α β) θ) (β ≫ τ) =
      gridMap₂ α β ⋙ nerveTriangleDiagram η θ τ := by
  unfold nerveTriangleDiagram
  rw [mk₂_whiskerLeft]
  rfl

/-- All-zero original grids give the literal constant triangle, by uniqueness of zero maps. -/
theorem nerveTriangleDiagram_eq_const_of_zero (η : A ⟶ B) (θ : B ⟶ C)
    (Z : D) (hZ : IsZero Z) (hA : ∀ p, A.obj p = Z) (hB : ∀ p, B.obj p = Z)
    (hC : ∀ p, C.obj p = Z) (τ : m ⟶ ⦋2⦌) :
    nerveTriangleDiagram η θ τ = (Functor.const (Grid₂ n m)).obj Z := by
  have hobj (p : Grid₂ n m) : (nerveTriangleDiagram η θ τ).obj p = Z := by
    change ((ComposableArrows.mk₂ η θ).obj (τ.toOrderHom p.1)).obj p = Z
    generalize τ.toOrderHom p.1 = a
    fin_cases a
    · exact hA p
    · exact hB p
    · exact hC p
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q f
  exact (hZ.of_iso (eqToIso (hobj q))).eq_of_tgt _ _

/-- The first face is exactly its original categorical nerve cylinder. -/
@[simp]
theorem nerveTriangleDiagram_first (η : A ⟶ B) (θ : B ⟶ C) (τ : m ⟶ ⦋1⦌) :
    nerveTriangleDiagram η θ (τ ≫ SimplexCategory.δ 2) = nerveCylinderDiagram η τ := by
  exact congrArg (fun K : ComposableArrows (Grid₂ n m ⥤ D) 1 ↦
    ((nerveTimeFunctor n τ).prod' (𝟭 (Grid₂ n m))) ⋙ Functor.uncurry.obj K)
      (nerve.δ₂_mk₂_eq η θ)

/-- The second face is exactly its original categorical nerve cylinder. -/
@[simp]
theorem nerveTriangleDiagram_second (η : A ⟶ B) (θ : B ⟶ C) (τ : m ⟶ ⦋1⦌) :
    nerveTriangleDiagram η θ (τ ≫ SimplexCategory.δ 0) = nerveCylinderDiagram θ τ := by
  exact congrArg (fun K : ComposableArrows (Grid₂ n m ⥤ D) 1 ↦
    ((nerveTimeFunctor n τ).prod' (𝟭 (Grid₂ n m))) ⋙ Functor.uncurry.obj K)
      (nerve.δ₀_mk₂_eq η θ)

/-- The composite face is exactly its original categorical nerve cylinder. -/
@[simp]
theorem nerveTriangleDiagram_composite (η : A ⟶ B) (θ : B ⟶ C) (τ : m ⟶ ⦋1⦌) :
    nerveTriangleDiagram η θ (τ ≫ SimplexCategory.δ 1) = nerveCylinderDiagram (η ≫ θ) τ := by
  exact congrArg (fun K : ComposableArrows (Grid₂ n m ⥤ D) 1 ↦
    ((nerveTimeFunctor n τ).prod' (𝟭 (Grid₂ n m))) ⋙ Functor.uncurry.obj K)
      (nerve.δ₁_mk₂_eq η θ)

/-- Original endpoint equalities and component equalities identify the actual triangles. -/
theorem nerveTriangleDiagram_congr_app {A' B' C' : Grid₂ n m ⥤ D}
    (η : A ⟶ B) (θ : B ⟶ C) (η' : A' ⟶ B') (θ' : B' ⟶ C')
    (hA : A = A') (hB : B = B') (hC : C = C')
    (hη : ∀ p, HEq (η.app p) (η'.app p)) (hθ : ∀ p, HEq (θ.app p) (θ'.app p))
    (τ : m ⟶ ⦋2⦌) : nerveTriangleDiagram η θ τ = nerveTriangleDiagram η' θ' τ := by
  subst A'
  subst B'
  subst C'
  have eη : η = η' := by
    ext p
    exact eq_of_heq (hη p)
  have eθ : θ = θ' := by
    ext p
    exact eq_of_heq (hθ p)
  rw [eη, eθ]

end CategoryTheory.Waldhausen
