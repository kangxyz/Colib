/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.Cofibration

/-!
# Relative homotopy inverses under a fixed base
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/RelativeInverse.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, homotopies and
pushout universal properties are retained, with native namespace and import ownership.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat

/-- A homotopy whose restriction is a backtracking path can be made relative
using HEP. The endpoints of the original homotopy are preserved. -/
theorem homotopyExtensionProperty_relative_of_backtrack {A B Z : TopCat.{u}}
    {i : A ⟶ B} (hi : TopCat.HomotopyExtensionProperty i) {f g : B ⟶ Z}
    (K : TopCat.Homotopy f g) (L : C(unitInterval × A, Z))
    (hL : ∀ a, L (1, a) = f (i a))
    (hK : ∀ t a, K (t, i a) = L (TopCat.backtrackTime t, a)) :
    Nonempty (f.hom.HomotopyRel g.hom (Set.range i)) := by
  let Kc : C(B, C(unitInterval, Z)) :=
    (K.toContinuousMap.comp ContinuousMap.prodSwap).curry
  let G : C((unitInterval × A) × unitInterval, Z) :=
    ⟨fun p ↦ L (TopCat.shrinkBacktrackTime p.1.1 p.2, p.1.2),
      L.continuous.comp ((TopCat.continuous_shrinkBacktrackTime.comp
        (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd)⟩
  have hG₀ : ∀ a, G.curry (0, a) = Kc (i a) := by
    intro a
    ext t
    change L (TopCat.shrinkBacktrackTime 0 t, a) = K (t, i a)
    rw [TopCat.shrinkBacktrackTime_zero]
    exact (hK t a).symm
  obtain ⟨Q, hQ₀, hQ⟩ := TopCat.homotopyExtensionProperty_continuous hi
    (TopCat.of C(unitInterval, Z)) Kc G.curry hG₀
  let e₀ : C(B, Z) := ⟨fun b ↦ Q (1, b) 0, by fun_prop⟩
  let e₁ : C(B, Z) := ⟨fun b ↦ Q (1, b) 1, by fun_prop⟩
  let L₀ : f.hom.Homotopy e₀ := {
    toFun := fun p ↦ Q p 0
    continuous_toFun := by fun_prop
    map_zero_left := fun b ↦ by
      rw [hQ₀]
      exact K.map_zero_left b
    map_one_left := fun _ ↦ rfl }
  let L₁ : e₀.Homotopy e₁ := {
    toFun := fun p ↦ Q (1, p.2) p.1
    continuous_toFun := by fun_prop
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun _ ↦ rfl }
  let L₂ : e₁.Homotopy g.hom := {
    toFun := fun p ↦ Q (unitInterval.symm p.1, p.2) 1
    continuous_toFun := by fun_prop
    map_zero_left := fun b ↦ by simp [e₁]
    map_one_left := fun b ↦ by
      rw [unitInterval.symm_one, hQ₀]
      exact K.map_one_left b }
  have hL₀ : ∀ t a, L₀ (t, i a) = f (i a) := by
    intro t a
    change Q (t, i a) 0 = f (i a)
    rw [hQ]
    change L (TopCat.shrinkBacktrackTime t 0, a) = f (i a)
    simpa using hL a
  have hL₁ : ∀ t a, L₁ (t, i a) = f (i a) := by
    intro t a
    change Q (1, i a) t = f (i a)
    rw [hQ]
    change L (TopCat.shrinkBacktrackTime 1 t, a) = f (i a)
    simpa using hL a
  have hL₂ : ∀ t a, L₂ (t, i a) = f (i a) := by
    intro t a
    change Q (unitInterval.symm t, i a) 1 = f (i a)
    rw [hQ]
    change L (TopCat.shrinkBacktrackTime (unitInterval.symm t) 1, a) = f (i a)
    simpa using hL a
  let R₀ : f.hom.HomotopyRel e₀ (Set.range i) := {
    toHomotopy := L₀
    prop' := by rintro t _ ⟨a, rfl⟩; exact hL₀ t a }
  let R₁ : e₀.HomotopyRel e₁ (Set.range i) := {
    toHomotopy := L₁
    prop' := by
      rintro t _ ⟨a, rfl⟩
      exact (hL₁ t a).trans (hL₀ 1 a).symm }
  let R₂ : e₁.HomotopyRel g.hom (Set.range i) := {
    toHomotopy := L₂
    prop' := by
      rintro t _ ⟨a, rfl⟩
      exact (hL₂ t a).trans (hL₁ 1 a).symm }
  exact ⟨(R₀.trans R₁).trans R₂⟩

/-- An actual homotopy equivalence under a cofibrant base has a strict left
inverse under the base, with a homotopy fixed on the base. -/
theorem homotopyExtensionProperty_exists_relative_left_inverse
    {A B C : TopCat.{u}} {i : A ⟶ B} {j : A ⟶ C}
    (hi : TopCat.HomotopyExtensionProperty i) (hj : TopCat.HomotopyExtensionProperty j)
    (e : ContinuousMap.HomotopyEquiv B C) (w : i ≫ TopCat.ofHom e.toFun = j) :
    ∃ r : C ⟶ B, j ≫ r = i ∧
      Nonempty ((TopCat.ofHom e.toFun ≫ r).hom.HomotopyRel
        (ContinuousMap.id B) (Set.range i)) ∧
      Nonempty (TopCat.Homotopy (r ≫ TopCat.ofHom e.toFun) (𝟙 C)) := by
  let f : B ⟶ C := TopCat.ofHom e.toFun
  let r₀ : C ⟶ B := TopCat.ofHom e.invFun
  let η : TopCat.Homotopy (f ≫ r₀) (𝟙 B) := e.left_inv.some
  let H := η.comp (TopCat.Homotopy.refl i)
  have hH₀ : TopCat.ι₀ ≫ H.h = j ≫ r₀ := by
    rw [H.ι₀_h, ← Category.assoc, w]
  obtain ⟨K, hK₀, hK⟩ := hj B r₀ H.h hH₀
  let r : C ⟶ B := TopCat.ι₁ ≫ K
  have hr : j ≫ r = i := by
    dsimp [r]
    rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hK, H.ι₁_h]
    simp
  let T : TopCat.Homotopy r₀ r := TopCat.homotopyOfCylinder K hK₀ rfl
  let F : TopCat.Homotopy (f ≫ r) (𝟙 B) :=
    (T.comp (TopCat.Homotopy.refl f)).symm.trans η
  have hT : ∀ t a, T (t, j a) = η (t, i a) := by
    intro t a
    exact ConcreteCategory.congr_hom hK (a, ULift.up t)
  have hFi : ∀ t a, F (t, i a) = η (TopCat.backtrackTime t, i a) := by
    intro t a
    have hw : f (i a) = j a := ConcreteCategory.congr_hom w a
    simp only [F, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change T (unitInterval.symm ⟨2 * (t : ℝ), _⟩, f (i a)) = _
      rw [hw, hT]
      congr 2
      apply Subtype.ext
      dsimp [TopCat.backtrackTime, unitInterval.symm]
      rw [abs_of_nonpos (by linarith)]
      ring
    · change η (⟨2 * (t : ℝ) - 1, _⟩, i a) = _
      congr 2
      apply Subtype.ext
      dsimp [TopCat.backtrackTime]
      rw [abs_of_nonneg (by linarith)]
  have hη : ∀ a, H.toContinuousMap (1, a) = (f ≫ r) (i a) := by
    intro a
    change η (1, i a) = r (f (i a))
    change η.toFun (1, i a) = _
    rw [η.map_one_left]
    have hw : f (i a) = j a := ConcreteCategory.congr_hom w a
    rw [hw]
    exact (ConcreteCategory.congr_hom hr a).symm
  refine ⟨r, hr,
    TopCat.homotopyExtensionProperty_relative_of_backtrack hi F H.toContinuousMap hη hFi, ⟨?_⟩⟩
  exact ((TopCat.Homotopy.refl f).comp T.symm).trans e.right_inv.some

/-- A homotopy equivalence between two spaces under the same cofibrant base
has a strict inverse under that base and both inverse homotopies relative
to the base. No relative inverse or coherent homotopy is assumed. -/
theorem homotopyExtensionProperty_exists_relative_inverse
    {A B C : TopCat.{u}} {i : A ⟶ B} {j : A ⟶ C}
    (hi : TopCat.HomotopyExtensionProperty i) (hj : TopCat.HomotopyExtensionProperty j)
    (e : ContinuousMap.HomotopyEquiv B C) (w : i ≫ TopCat.ofHom e.toFun = j) :
    ∃ r : C ⟶ B, j ≫ r = i ∧
      Nonempty ((TopCat.ofHom e.toFun ≫ r).hom.HomotopyRel
        (ContinuousMap.id B) (Set.range i)) ∧
      Nonempty ((r ≫ TopCat.ofHom e.toFun).hom.HomotopyRel
        (ContinuousMap.id C) (Set.range j)) := by
  let f : B ⟶ C := TopCat.ofHom e.toFun
  obtain ⟨r, hr, ⟨L⟩, ⟨R⟩⟩ :=
    TopCat.homotopyExtensionProperty_exists_relative_left_inverse hi hj e w
  let er : ContinuousMap.HomotopyEquiv C B :=
    ⟨r.hom, f.hom, ⟨R⟩, ⟨L.toHomotopy⟩⟩
  obtain ⟨s, hs, ⟨M⟩, _⟩ :=
    TopCat.homotopyExtensionProperty_exists_relative_left_inverse hj hi er hr
  have hri : ∀ a, r (j a) = i a := fun a ↦ ConcreteCategory.congr_hom hr a
  have hfi : ∀ a, f (i a) = j a := fun a ↦ ConcreteCategory.congr_hom w a
  have hsi : ∀ a, s (i a) = j a := fun a ↦ ConcreteCategory.congr_hom hs a
  let R₀ : (r ≫ f).hom.HomotopyRel (r ≫ f ≫ r ≫ s).hom (Set.range j) := {
    toHomotopy := (M.toHomotopy.compContinuousMap (r ≫ f).hom).symm
    prop' := by
      rintro t _ ⟨a, rfl⟩
      change M.toHomotopy (unitInterval.symm t, f (r (j a))) = f (r (j a))
      rw [hri, hfi]
      exact M.eq_snd _ ⟨a, rfl⟩ }
  let R₁ : (r ≫ f ≫ r ≫ s).hom.HomotopyRel (r ≫ s).hom (Set.range j) := {
    toHomotopy := (TopCat.Homotopy.refl s).comp
      (L.toHomotopy.compContinuousMap r.hom)
    prop' := by
      rintro t _ ⟨a, rfl⟩
      change s (L.toHomotopy (t, r (j a))) = s (r (f (r (j a))))
      rw [hri, hfi, hri]
      exact congrArg s (L.eq_snd t ⟨a, rfl⟩) }
  refine ⟨r, hr, ⟨L⟩, ⟨?_⟩⟩
  exact (R₀.trans R₁).trans M


end TopCat
