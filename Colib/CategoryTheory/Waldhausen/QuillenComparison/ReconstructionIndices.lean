/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.RowChain
public import Mathlib.CategoryTheory.ComposableArrows.Basic


/-! # Recursive central intervals and terminal extension of chain isomorphisms -/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.ComposableArrows
open scoped Simplicial
universe u v

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows SSet

/-- The old edgewise ordinal sits in the new one between its two new endpoints. -/
def reconstructionMiddleOrdinal (n : ℕ) : EdgewiseSubdivision.ε.obj ⦋n⦌ ⟶ EdgewiseSubdivision.ε.obj
  ⦋n + 1⦌ :=
  SimplexCategory.Hom.mk {
    toFun k := ⟨k.val + 1, by
      have hk := k.isLt
      change k.val < n + n + 1 + 1 at hk
      change k.val + 1 < (n + 1) + (n + 1) + 1 + 1
      omega⟩
    monotone' := fun _ _ h ↦ Nat.add_le_add_right h 1 }

@[simp]
theorem reconstructionMiddleOrdinal_val (n : ℕ)
    (k : Fin ((EdgewiseSubdivision.ε.obj ⦋n⦌).len + 1)) :
    ((reconstructionMiddleOrdinal n).toOrderHom k).val = k.val + 1 := rfl

/-- The two additional flag terms are precisely the growth of the edgewise ordinal. -/
theorem reconstructionMiddle_size (n : ℕ) :
    (EdgewiseSubdivision.ε.obj ⦋n⦌).len + 1 + 1 + 1 =
      (EdgewiseSubdivision.ε.obj ⦋n + 1⦌).len + 1 := by
  change n + n + 1 + 1 + 1 + 1 = (n + 1) + (n + 1) + 1 + 1
  omega

/-- Compatibility with the literal middle indices used by extendedPullbackFlag. -/
theorem reconstructionMiddleOrdinal_eq_castSucc_succ (n : ℕ)
    (k : Fin ((EdgewiseSubdivision.ε.obj ⦋n⦌).len + 1)) :
    (reconstructionMiddleOrdinal n).toOrderHom k =
      Fin.cast (reconstructionMiddle_size n) k.castSucc.succ := by
  apply Fin.ext
  rfl

@[simp]
theorem reconstructionMiddleOrdinal_lower (n : ℕ) (i : Fin (n + 1)) :
    (reconstructionMiddleOrdinal n).toOrderHom (lowerIndex ⦋n⦌ i) =
      lowerIndex ⦋n + 1⦌ i.castSucc := by
  apply Fin.ext
  simp only [reconstructionMiddleOrdinal_val, lowerIndex, OrdinalJoin.left_val, Fin.val_rev,
    Fin.val_castSucc, SimplexCategory.len_mk]
  have := i.isLt
  omega

@[simp]
theorem reconstructionMiddleOrdinal_upper (n : ℕ) (i : Fin (n + 1)) :
    (reconstructionMiddleOrdinal n).toOrderHom (upperIndex ⦋n⦌ i) =
      upperIndex ⦋n + 1⦌ i.castSucc := by
  apply Fin.ext
  change n + 1 + i.val + 1 = (n + 1) + 1 + i.val
  omega

/-- Every old central interval is exactly the corresponding new central interval. -/
@[simp]
theorem reconstructionMiddleOrdinal_central (n : ℕ) (i : Fin (n + 1)) :
    (nestedIntervalMap (reconstructionMiddleOrdinal n)).obj (centralInterval ⦋n⦌ i) =
      centralInterval ⦋n + 1⦌ i.castSucc :=
  Subtype.ext (Prod.ext (reconstructionMiddleOrdinal_lower n i)
    (reconstructionMiddleOrdinal_upper n i))

/-- The entire initial central chain is the old central chain after middle reindexing. -/
theorem reconstructionMiddle_centralFunctor (n : ℕ) :
    centralIntervalFunctor ⦋n⦌ ⋙ nestedIntervalMap (reconstructionMiddleOrdinal n) =
      Fin.castSuccFunctor (n + 1) ⋙ centralIntervalFunctor ⦋n + 1⦌ := by
  apply CategoryTheory.Functor.ext (fun i ↦ reconstructionMiddleOrdinal_central n i)

section Chains
variable {D : Type u} [Category.{v} D] {n : ℕ}
  {F G : ComposableArrows D (n + 1)}

/-- The displayed old components together with the new terminal component. -/
def chainIsoLastComponents
    (β : Fin.castSuccFunctor (n + 1) ⋙ F ≅ Fin.castSuccFunctor (n + 1) ⋙ G)
    (α : F.obj (Fin.last (n + 1)) ≅ G.obj (Fin.last (n + 1))) :
    ∀ i, F.obj i ≅ G.obj i :=
  Fin.lastCases α (fun i ↦ β.app i)

/-- Extend an isomorphism on the initial chain by a final object isomorphism.
Only the last adjacent square must be checked. -/
def chainIsoMkLast
    (β : Fin.castSuccFunctor (n + 1) ⋙ F ≅ Fin.castSuccFunctor (n + 1) ⋙ G)
    (α : F.obj (Fin.last (n + 1)) ≅ G.obj (Fin.last (n + 1)))
    (w : F.map' n (n + 1) ≫ α.hom =
      (β.app (Fin.last n)).hom ≫ G.map' n (n + 1)) : F ≅ G :=
  ComposableArrows.isoMk (chainIsoLastComponents β α) (by
    suffices ∀ (i : Fin (n + 1)),
        F.map (homOfLE (Fin.castSucc_le_succ i)) ≫
            (chainIsoLastComponents β α i.succ).hom =
          (chainIsoLastComponents β α i.castSucc).hom ≫
            G.map (homOfLE (Fin.castSucc_le_succ i)) by
      intro i hi
      exact this ⟨i, hi⟩
    intro i
    induction i using Fin.lastCases with
    | last =>
      simpa only [chainIsoLastComponents, Fin.succ_last, Fin.lastCases_last,
        Fin.lastCases_castSucc] using w
    | cast i =>
      simpa only [chainIsoLastComponents, ← Fin.castSucc_succ, Fin.lastCases_castSucc,
        Functor.comp_map, Fin.castSuccFunctor_map] using!
        β.hom.naturality (homOfLE (Fin.castSucc_le_succ i)))

@[simp]
theorem chainIsoMkLast_app_castSucc
    (β : Fin.castSuccFunctor (n + 1) ⋙ F ≅ Fin.castSuccFunctor (n + 1) ⋙ G)
    (α : F.obj (Fin.last (n + 1)) ≅ G.obj (Fin.last (n + 1)))
    (w : F.map' n (n + 1) ≫ α.hom =
      (β.app (Fin.last n)).hom ≫ G.map' n (n + 1)) (i : Fin (n + 1)) :
    (chainIsoMkLast β α w).app i.castSucc = β.app i := by
  apply Iso.ext
  change (chainIsoLastComponents β α i.castSucc).hom = (β.app i).hom
  simp only [chainIsoLastComponents, Fin.lastCases_castSucc]

@[simp]
theorem chainIsoMkLast_app_last
    (β : Fin.castSuccFunctor (n + 1) ⋙ F ≅ Fin.castSuccFunctor (n + 1) ⋙ G)
    (α : F.obj (Fin.last (n + 1)) ≅ G.obj (Fin.last (n + 1)))
    (w : F.map' n (n + 1) ≫ α.hom =
      (β.app (Fin.last n)).hom ≫ G.map' n (n + 1)) :
    (chainIsoMkLast β α w).app (Fin.last (n + 1)) = α := by
  apply Iso.ext
  change (chainIsoLastComponents β α (Fin.last (n + 1))).hom = α.hom
  simp only [chainIsoLastComponents, Fin.lastCases_last]

/-- Restricting the extended isomorphism recovers precisely the supplied initial isomorphism. -/
@[simp]
theorem chainIsoMkLast_restrict
    (β : Fin.castSuccFunctor (n + 1) ⋙ F ≅ Fin.castSuccFunctor (n + 1) ⋙ G)
    (α : F.obj (Fin.last (n + 1)) ≅ G.obj (Fin.last (n + 1)))
    (w : F.map' n (n + 1) ≫ α.hom =
      (β.app (Fin.last n)).hom ≫ G.map' n (n + 1)) :
    Functor.isoWhiskerLeft (Fin.castSuccFunctor (n + 1)) (chainIsoMkLast β α w) = β := by
  apply Iso.ext
  apply NatTrans.ext
  funext i
  exact congrArg Iso.hom (chainIsoMkLast_app_castSucc β α w i)

end Chains
end CategoryTheory.Waldhausen.QuillenComparison
