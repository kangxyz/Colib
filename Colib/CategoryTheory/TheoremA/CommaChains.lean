/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SimplicialReplacement

/-! Source: Quillen/CategoryTheory/TheoremA/CommaChains.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universal properties retained. -/

/-!
# Chains in comma categories

A chain in `(F ↓ d)` is exactly a chain `c₀ ⟶ ⋯ ⟶ cₙ` in the
source together with its final arrow `F(cₙ) ⟶ d`. This explicit bijection is
the categorical ingredient for identifying the other rows of the Theorem A
bisimplicial replacement with nerves of under categories.
-/
@[expose] public section

noncomputable section

open SSet CategoryTheory Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- A source chain and an arrow from its last object determine a comma chain. -/
def commaChainOfLast {d : D} {n : ℕ} (c : ComposableArrows C n)
    (h : F.obj (c.obj (Fin.last n)) ⟶ d) : ComposableArrows (CostructuredArrow F d) n where
  obj i := CostructuredArrow.mk (F.map (c.map (homOfLE (Fin.le_last i))) ≫ h)
  map {i j} f := CostructuredArrow.homMk (c.map f) (by
    dsimp
    rw [← F.map_comp_assoc, ← c.map_comp]
    rfl)
  map_id i := by
    apply CostructuredArrow.hom_ext
    exact c.map_id i
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact c.map_comp f g

/-- The final-arrow description of a chain of costructured arrows. -/
def commaChainEquiv (d : D) (n : ℕ) :
    ComposableArrows (CostructuredArrow F d) n ≃
      Σ c : ComposableArrows C n, F.obj (c.obj (Fin.last n)) ⟶ d where
  toFun x := ⟨x ⋙ CostructuredArrow.proj F d, (x.obj (Fin.last n)).hom⟩
  invFun x := commaChainOfLast F x.1 x.2
  left_inv x := by
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
    · refine CostructuredArrow.obj_ext _ _ rfl ?_
      dsimp [commaChainOfLast]
      rw [F.map_id, Category.id_comp]
      exact (CostructuredArrow.w (x.map (homOfLE (Fin.le_last i)))).symm
    · intro i j f
      apply CostructuredArrow.hom_ext
      simp [commaChainOfLast]
  right_inv x := by
    rcases x with ⟨c, h⟩
    dsimp only
    refine Sigma.ext (CategoryTheory.Functor.ext (fun _ ↦ rfl)) ?_
    apply heq_of_eq
    dsimp [commaChainOfLast]
    simp

/-- A source arrow into the first object determines a chain of structured arrows. -/
def structuredChainOfFirst {d : D} {n : ℕ} (c : ComposableArrows C n)
    (h : d ⟶ F.obj (c.obj 0)) : ComposableArrows (StructuredArrow d F) n where
  obj i := StructuredArrow.mk (h ≫ F.map (c.map (homOfLE (Fin.zero_le i))))
  map {i j} f := StructuredArrow.homMk (c.map f) (by
    dsimp
    rw [Category.assoc, ← F.map_comp, ← c.map_comp]
    rfl)
  map_id i := by
    apply StructuredArrow.hom_ext
    exact c.map_id i
  map_comp f g := by
    apply StructuredArrow.hom_ext
    exact c.map_comp f g

/-- The first-arrow description of a chain of structured arrows. -/
def structuredChainEquiv (d : D) (n : ℕ) :
    ComposableArrows (StructuredArrow d F) n ≃
      Σ c : ComposableArrows C n, d ⟶ F.obj (c.obj 0) where
  toFun x := ⟨x ⋙ StructuredArrow.proj d F, (x.obj 0).hom⟩
  invFun x := structuredChainOfFirst F x.1 x.2
  left_inv x := by
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
    · refine StructuredArrow.obj_ext _ _ rfl ?_
      dsimp [structuredChainOfFirst]
      rw [F.map_id, Category.comp_id]
      exact StructuredArrow.w (x.map (homOfLE (Fin.zero_le i)))
    · intro i j f
      apply StructuredArrow.hom_ext
      simp [structuredChainOfFirst]
  right_inv x := by
    rcases x with ⟨c, h⟩
    dsimp only
    refine Sigma.ext (CategoryTheory.Functor.ext (fun _ ↦ rfl)) ?_
    apply heq_of_eq
    dsimp [structuredChainOfFirst]
    change h ≫ F.map (c.map (𝟙 (0 : Fin (n + 1)))) = h
    simp

end CategoryTheory.TheoremA
