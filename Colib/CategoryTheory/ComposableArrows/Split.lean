/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.CategoryTheory.ComposableArrows.Restriction

/-!
# Split

Split the actual ordered chain at a specified vertex; the common object is
literally shared, not replaced by an unspecified equivalence.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u v
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- Embed the first subchain, including its terminal split vertex. -/
def leftIndex (m n : ℕ) (i : Fin (m + 1)) : Fin (m + n + 1) := ⟨i.val, by omega⟩
/-- Embed the second subchain, starting at the common split vertex. -/
def rightIndex (m n : ℕ) (i : Fin (n + 1)) : Fin (m + n + 1) := ⟨m + i.val, by omega⟩
theorem leftIndex_monotone (m n : ℕ) : Monotone (leftIndex m n) := by
  intro i j h
  exact h
theorem rightIndex_monotone (m n : ℕ) : Monotone (rightIndex m n) := by
  intro i j h
  exact Nat.add_le_add_left h m

/-- Split the actual ordered chain at a specified vertex; the common object is
literally shared, not replaced by an unspecified equivalence. -/
theorem finiteChainComp_split {m n : ℕ}
    (X : Fin (m + n + 1) → C)
    (f : ∀ i : Fin (m + n), X i.castSucc ⟶ X i.succ) :
    finiteChainComp X f =
      finiteChainComp (fun i => X (leftIndex m n i))
        (fun i : Fin m => f ⟨i.val, by omega⟩) ≫
      finiteChainComp (fun i => X (rightIndex m n i))
        (fun i : Fin n => f ⟨m + i.val, by omega⟩) := by
  let F := ComposableArrows.mkOfObjOfMapSucc X f
  have hl := finiteChainComp_restriction F (leftIndex m n) (leftIndex_monotone m n)
  have hr := finiteChainComp_restriction F (rightIndex m n) (rightIndex_monotone m n)
  have hl' : finiteChainComp (fun i => X (leftIndex m n i))
      (fun i : Fin m => f ⟨i.val, by omega⟩) =
      F.map (homOfLE ((leftIndex_monotone m n) (Fin.zero_le (Fin.last m)))) := by
    refine Eq.trans ?_ hl
    apply congrArg (finiteChainComp (fun i => X (leftIndex m n i)))
    funext i
    exact (ComposableArrows.mkOfObjOfMapSucc_map_succ X f i.val (by omega)).symm
  have hr' : finiteChainComp (fun i => X (rightIndex m n i))
      (fun i : Fin n => f ⟨m + i.val, by omega⟩) =
      F.map (homOfLE ((rightIndex_monotone m n) (Fin.zero_le (Fin.last n)))) := by
    refine Eq.trans ?_ hr
    apply congrArg (finiteChainComp (fun i => X (rightIndex m n i)))
    funext i
    exact (ComposableArrows.mkOfObjOfMapSucc_map_succ X f (m + i.val) (by omega)).symm
  rw [hl', hr', ← F.map_comp]
  rfl

end CategoryTheory
