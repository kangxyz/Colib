/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.Basic
public import Colib.Topology.Homotopy.RelativeInverse

/-!
# Relative homotopy gluing on topological pushouts
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Pushout/Homotopy.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, homotopies and
pushout universal properties are retained, with native namespace and import ownership.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat

/-- A relative homotopy on one side of a topological pushout extends by the
constant homotopy on the other side. -/
def Pushout.pushoutHomotopyOfRelative {A B C D Z : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) {u₀ u₁ : D ⟶ Z}
    (H : TopCat.Homotopy (g ≫ u₀) (g ≫ u₁))
    (hH : ∀ t a, H (t, i a) = u₀ (g (i a)))
    (hj : j ≫ u₀ = j ≫ u₁) : TopCat.Homotopy u₀ u₁ := by
  have sqI : IsPushout (i ▷ TopCat.I) (f ▷ TopCat.I)
      (g ▷ TopCat.I) (j ▷ TopCat.I) := sq.map (tensorRight TopCat.I)
  have hw : (i ▷ TopCat.I) ≫ H.h =
      (f ▷ TopCat.I) ≫ fst C TopCat.I ≫ j ≫ u₀ := by
    ext ⟨a, t⟩
    change H (t.down, i a) = u₀ (j (f a))
    rw [hH]
    exact congrArg u₀ (ConcreteCategory.congr_hom sq.w a)
  let K := sqI.desc H.h (fst C TopCat.I ≫ j ≫ u₀) hw
  have hgK : (g ▷ TopCat.I) ≫ K = H.h := sqI.inl_desc _ _ _
  have hjK : (j ▷ TopCat.I) ≫ K = fst C TopCat.I ≫ j ≫ u₀ := sqI.inr_desc _ _ _
  apply TopCat.homotopyOfCylinder K
  · apply sq.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hgK, H.ι₀_h]
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hjK,
        ← Category.assoc, TopCat.ι₀_fst, Category.id_comp]
  · apply sq.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hgK, H.ι₁_h]
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hjK,
        ← Category.assoc, TopCat.ι₁_fst, Category.id_comp, hj]

/-- Changing one cofibrant side of a pushout by an actual homotopy
equivalence over the fixed common base preserves its homotopy type.
The other attaching map is arbitrary. -/
def Pushout.pushoutHomotopyEquivOverBase {A B B' C D D' : TopCat.{u}}
    {i : A ⟶ B} {i' : A ⟶ B'} {f : A ⟶ C}
    {g : B ⟶ D} {j : C ⟶ D} {g' : B' ⟶ D'} {j' : C ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f g' j')
    (hi : TopCat.HomotopyExtensionProperty i) (hi' : TopCat.HomotopyExtensionProperty i')
    (e : ContinuousMap.HomotopyEquiv B B') (w : i ≫ TopCat.ofHom e.toFun = i') :
    ContinuousMap.HomotopyEquiv D D' := by
  let b : B ⟶ B' := TopCat.ofHom e.toFun
  let h := TopCat.homotopyExtensionProperty_exists_relative_inverse hi hi' e w
  let r := h.choose
  have hr : i' ≫ r = i := h.choose_spec.1
  let L := h.choose_spec.2.1.some
  let R := h.choose_spec.2.2.some
  have hw : i ≫ b ≫ g' = f ≫ j' := by rw [← Category.assoc, w, sq'.w]
  have hw' : i' ≫ r ≫ g = f ≫ j := by rw [← Category.assoc, hr, sq.w]
  let p : D ⟶ D' := sq.desc (b ≫ g') j' hw
  let q : D' ⟶ D := sq'.desc (r ≫ g) j hw'
  have hgp : g ≫ p = b ≫ g' := sq.inl_desc _ _ _
  have hjp : j ≫ p = j' := sq.inr_desc _ _ _
  have hgq : g' ≫ q = r ≫ g := sq'.inl_desc _ _ _
  have hjq : j' ≫ q = j := sq'.inr_desc _ _ _
  have hgpq : g ≫ p ≫ q = b ≫ r ≫ g := by rw [← Category.assoc, hgp, Category.assoc, hgq]
  have hgqp : g' ≫ q ≫ p = r ≫ b ≫ g' := by rw [← Category.assoc, hgq, Category.assoc, hgp]
  let HL : TopCat.Homotopy (g ≫ p ≫ q) (g ≫ 𝟙 D) :=
    ((TopCat.Homotopy.refl g).comp L.toHomotopy).cast
      (congrArg TopCat.Hom.hom hgpq).symm (by ext; rfl)
  let HR : TopCat.Homotopy (g' ≫ q ≫ p) (g' ≫ 𝟙 D') :=
    ((TopCat.Homotopy.refl g').comp R.toHomotopy).cast
      (congrArg TopCat.Hom.hom hgqp).symm (by ext; rfl)
  refine ⟨p.hom, q.hom, ⟨TopCat.Pushout.pushoutHomotopyOfRelative sq HL ?_ ?_⟩,
    ⟨TopCat.Pushout.pushoutHomotopyOfRelative sq' HR ?_ ?_⟩⟩
  · intro t a
    change g (L.toHomotopy (t, i a)) = (p ≫ q) (g (i a))
    calc
      _ = g ((b ≫ r) (i a)) := congrArg g (L.eq_fst t ⟨a, rfl⟩)
      _ = (p ≫ q) (g (i a)) := (ConcreteCategory.congr_hom hgpq (i a)).symm
  · change j ≫ p ≫ q = j ≫ 𝟙 D
    rw [← Category.assoc, hjp, hjq, Category.comp_id]
  · intro t a
    change g' (R.toHomotopy (t, i' a)) = (q ≫ p) (g' (i' a))
    calc
      _ = g' ((r ≫ b) (i' a)) := congrArg g' (R.eq_fst t ⟨a, rfl⟩)
      _ = (q ≫ p) (g' (i' a)) := (ConcreteCategory.congr_hom hgqp (i' a)).symm
  · change j' ≫ q ≫ p = j' ≫ 𝟙 D'
    rw [← Category.assoc, hjq, hjp, Category.comp_id]

@[simp]
theorem Pushout.pushoutHomotopyEquivOverBase_toFun {A B B' C D D' : TopCat.{u}}
    {i : A ⟶ B} {i' : A ⟶ B'} {f : A ⟶ C}
    {g : B ⟶ D} {j : C ⟶ D} {g' : B' ⟶ D'} {j' : C ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f g' j')
    (hi : TopCat.HomotopyExtensionProperty i) (hi' : TopCat.HomotopyExtensionProperty i')
    (e : ContinuousMap.HomotopyEquiv B B') (w : i ≫ TopCat.ofHom e.toFun = i') :
    (TopCat.Pushout.pushoutHomotopyEquivOverBase sq sq' hi hi' e w).toFun =
      (sq.desc (TopCat.ofHom e.toFun ≫ g') j' (by rw [← Category.assoc, w, sq'.w])).hom := rfl


end TopCat
