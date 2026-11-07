/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Grid

Compose a finite chain in its given order; an empty chain is an identity.
-/

@[expose] public section

/-!
Finite rectangular pasting of actual morphisms. This is only a categorical
pasting lemma, not a completeness assertion for geometric path relations.
-/

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Compose a finite chain in its given order; an empty chain is an identity. -/
noncomputable def finiteChainComp {n : ℕ} (X : Fin (n + 1) → C)
    (f : ∀ i : Fin n, X i.castSucc ⟶ X i.succ) : X 0 ⟶ X (Fin.last n) :=
  (ComposableArrows.mkOfObjOfMapSucc X f).map (homOfLE (Fin.zero_le _))

set_option backward.isDefEq.respectTransparency false in
/-- Pasting a finite row of squares, including the empty row. -/
theorem finiteChainCommSq {n : ℕ} (X Y : Fin (n + 1) → C)
    (f : ∀ i : Fin n, X i.castSucc ⟶ X i.succ)
    (g : ∀ i : Fin n, Y i.castSucc ⟶ Y i.succ)
    (e : ∀ i, X i ⟶ Y i)
    (sq : ∀ i : Fin n, CommSq (f i) (e i.castSucc) (e i.succ) (g i)) :
    CommSq (finiteChainComp X f) (e 0) (e (Fin.last n)) (finiteChainComp Y g) := by
  let F := ComposableArrows.mkOfObjOfMapSucc X f
  let G := ComposableArrows.mkOfObjOfMapSucc Y g
  let α : F ⟶ G := ComposableArrows.homMk e (by
    intro i hi
    simpa only [F, G, ComposableArrows.mkOfObjOfMapSucc_map_succ] using! (sq ⟨i, hi⟩).w)
  exact ⟨α.naturality (homOfLE (Fin.zero_le (Fin.last n)))⟩

/-- The boundary of a finite rectangular grid commutes if every cell does.
Neither positive dimensions, distinct vertices nor invertible arrows are needed. -/
theorem finiteGridCommSq {m n : ℕ} (X : Fin (m + 1) → Fin (n + 1) → C)
    (h : ∀ i, ∀ j : Fin n, X i j.castSucc ⟶ X i j.succ)
    (v : ∀ i : Fin m, ∀ j, X i.castSucc j ⟶ X i.succ j)
    (sq : ∀ (i : Fin m) (j : Fin n),
      CommSq (h i.castSucc j) (v i j.castSucc) (v i j.succ) (h i.succ j)) :
    CommSq (finiteChainComp (X 0) (h 0))
      (finiteChainComp (fun i => X i 0) (fun i => v i 0))
      (finiteChainComp (fun i => X i (Fin.last n)) (fun i => v i (Fin.last n)))
      (finiteChainComp (X (Fin.last m)) (h (Fin.last m))) := by
  exact (finiteChainCommSq (fun i => X i 0) (fun i => X i (Fin.last n))
    (fun i => v i 0) (fun i => v i (Fin.last n))
    (fun i => finiteChainComp (X i) (h i))
    (fun i => (finiteChainCommSq (X i.castSucc) (X i.succ)
      (h i.castSucc) (h i.succ) (v i) (sq i)).flip)).flip

end CategoryTheory
