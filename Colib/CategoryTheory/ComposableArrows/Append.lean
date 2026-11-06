/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Appending an arrow to an actual finite chain

The construction needs only a category. It preserves every old object and map,
and the map to the new last object is exactly the old top map followed by the
given arrow. The original-index restriction is supplied as an explicit isomorphism.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
universe u v
namespace CategoryTheory.ComposableArrows
section Append
variable {C : Type u} [Category.{v} C] {n : ℕ} (A : ComposableArrows C n) {Y : C}
variable (q : A.obj (Fin.last n) ⟶ Y)
/-- The object sequence obtained by adjoining a last target. -/
def appendChainObj : Fin (n + 1 + 1) → C := Fin.lastCases Y A.obj

@[simp]
theorem appendChainObj_castSucc (i : Fin (n + 1)) :
    appendChainObj A (Y := Y) i.castSucc = A.obj i := Fin.lastCases_castSucc i

@[simp]
theorem appendChainObj_last : appendChainObj A (Y := Y) (Fin.last (n + 1)) = Y :=
  Fin.lastCases_last

@[simp]
theorem appendChainObj_succ_castSucc (i : Fin n) :
    appendChainObj A (Y := Y) i.castSucc.succ = A.obj i.succ := by
  rw [← Fin.castSucc_succ, appendChainObj_castSucc]

/-- The old neighboring maps followed by the prescribed last map. -/
def appendChainSucc (i : Fin (n + 1)) :
    appendChainObj A (Y := Y) i.castSucc ⟶ appendChainObj A (Y := Y) i.succ :=
  Fin.lastCases
    (eqToHom (appendChainObj_castSucc A (Fin.last n)) ≫ q ≫
      eqToHom (by simp only [Fin.succ_last, appendChainObj_last]))
    (fun j ↦ eqToHom (appendChainObj_castSucc A j.castSucc) ≫
      A.map (homOfLE (Fin.castSucc_le_succ j)) ≫
      eqToHom (appendChainObj_succ_castSucc A j).symm) i

/-- Append a target using the actual adjacent flag maps. -/
def appendChain : ComposableArrows C (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc (appendChainObj A (Y := Y)) (appendChainSucc A q)

@[simp]
theorem appendChain_obj_castSucc (i : Fin (n + 1)) :
    (appendChain A q).obj i.castSucc = A.obj i := appendChainObj_castSucc A i

@[simp]
theorem appendChain_obj_last : (appendChain A q).obj (Fin.last (n + 1)) = Y :=
  appendChainObj_last A

/-- Restricting the appended flag to its original indices canonically recovers it. -/
def appendChainRestrictionIso :
    Fin.castSuccFunctor (n + 1) ⋙ appendChain A q ≅ A :=
  ComposableArrows.isoMk (fun i ↦ eqToIso (appendChain_obj_castSucc A q i)) (by
    intro i hi
    change (appendChain A q).map' i (i + 1) ≫ _ = _ ≫ A.map' i (i + 1)
    rw [show (appendChain A q).map' i (i + 1) = appendChainSucc A q ⟨i, by omega⟩ from
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i (by omega)]
    change appendChainSucc A q (Fin.castSucc ⟨i, hi⟩) ≫ _ = _
    simp only [appendChainSucc, Fin.lastCases_castSucc, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id, eqToIso.hom])

/-- The appended adjacent arrow is the prescribed target map, under the object identifications. -/
theorem appendChain_last_step :
    (appendChain A q).map (homOfLE (Fin.le_last (Fin.last n).castSucc)) ≫
        eqToHom (appendChain_obj_last A q) =
      eqToHom (appendChain_obj_castSucc A q (Fin.last n)) ≫ q := by
  change (appendChain A q).map' n (n + 1) ≫ _ = _
  rw [show (appendChain A q).map' n (n + 1) = appendChainSucc A q (Fin.last n) from
    ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ n (by omega)]
  simp [appendChainSucc]

/-- The maps to the appended target are the old top maps followed by the prescribed map. -/
theorem appendChain_to_last (i : Fin (n + 1)) :
    (appendChain A q).map (homOfLE (Fin.le_last i.castSucc)) ≫
        eqToHom (appendChain_obj_last A q) =
      eqToHom (appendChain_obj_castSucc A q i) ≫ A.map (homOfLE (Fin.le_last i)) ≫ q := by
  let f : i ⟶ Fin.last n := homOfLE (Fin.le_last i)
  have h := (appendChainRestrictionIso A q).hom.naturality f
  change (appendChain A q).map ((Fin.castSuccFunctor (n + 1)).map f) ≫
      eqToHom (appendChain_obj_castSucc A q (Fin.last n)) =
    eqToHom (appendChain_obj_castSucc A q i) ≫ A.map (homOfLE (Fin.le_last i)) at h
  rw [show homOfLE (Fin.le_last i.castSucc) =
    (Fin.castSuccFunctor (n + 1)).map f ≫
      homOfLE (Fin.le_last (Fin.last n).castSucc) from Subsingleton.elim _ _,
    Functor.map_comp, Category.assoc, appendChain_last_step, ← Category.assoc, h,
    Category.assoc]


end Append
end CategoryTheory.ComposableArrows
