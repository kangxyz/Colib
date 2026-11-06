/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.CategoryTheory.ComposableArrows.Grid

/-!
# Restriction

The actual ordered chain of a functor's adjacent arrows is its total arrow.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u v
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- The actual ordered chain of a functor's adjacent arrows is its total arrow. -/
theorem finiteChainComp_functor {n : ℕ} (F : Fin (n + 1) ⥤ C) :
    finiteChainComp F.obj (fun i => F.map (homOfLE (Fin.castSucc_le_succ i))) =
      F.map (homOfLE (Fin.zero_le (Fin.last n))) := by
  let K := ComposableArrows.mkOfObjOfMapSucc F.obj
    (fun i => F.map (homOfLE (Fin.castSucc_le_succ i)))
  let α : K ⟶ F := ComposableArrows.homMk (fun j => 𝟙 (F.obj j)) (by
    intro i hi
    simp only [K, ComposableArrows.mkOfObjOfMapSucc_map_succ]
    change F.map (homOfLE (show (⟨i, by omega⟩ : Fin (n + 1)) ≤
      ⟨i + 1, by omega⟩ by exact Nat.le_succ i)) ≫ 𝟙 _ =
      𝟙 _ ≫ F.map (homOfLE (by exact Nat.le_succ i))
    simp only [Category.comp_id, Category.id_comp])
  have h := α.naturality (homOfLE (Fin.zero_le (Fin.last n)))
  change K.map (homOfLE (Fin.zero_le (Fin.last n))) ≫ 𝟙 _ =
    𝟙 _ ≫ F.map (homOfLE (Fin.zero_le (Fin.last n))) at h
  simpa only [Category.comp_id, Category.id_comp] using! h

/-- Restriction computes precisely the original functor's endpoint arrow. -/
theorem finiteChainComp_restriction {m n : ℕ} (F : Fin (m + 1) ⥤ C)
    (r : Fin (n + 1) → Fin (m + 1)) (hr : Monotone r) :
    finiteChainComp (fun i => F.obj (r i))
      (fun i => F.map (homOfLE (hr (Fin.castSucc_le_succ i)))) =
      F.map (homOfLE (hr (Fin.zero_le (Fin.last n)))) :=
  finiteChainComp_functor ((hr.functor ⋙ F))

end CategoryTheory
