/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.Cofibration
public import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Sequential composites of strong deformation retractions

The deformation of each new stage is placed before the already constructed
homotopy, in a shrinking initial time interval. On each fixed stage the
result is stationary near time zero. The homotopies therefore agree exactly
on successive stages and descend through the actual topological colimit.
-/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremA/RealizationSequentialDeformation.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, prescribed forward
comparisons, deformation homotopies, hypotheses and universes are retained.
Only namespace/import ownership and unnecessary broad imports change.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

namespace TopCat

attribute [local instance] Classical.propDecidable

/-- Deformation data with a prescribed initial stationary interval. -/
structure TimedDeformationRetract {A B : TopCat.{u}} (i : A ⟶ B) (δ : ℝ) where
  /-- The retraction from `B` to `A`, a left inverse to the inclusion `i`. -/
  r : B ⟶ A
  retract : i ≫ r = 𝟙 A
  /-- The homotopy from the identity of `B` to `r ≫ i`, fixing the image of `A` and remaining
  stationary through time `δ`. -/
  H : TopCat.Homotopy (𝟙 B) (r ≫ i)
  fixed : ∀ t a, H (t, i a) = i a
  stationary : ∀ (t : unitInterval) b, (t : ℝ) ≤ δ → H (t, b) = b

/-- A constant deformation can wait for any amount of time. -/
def TimedDeformationRetract.id (A : TopCat.{u}) (δ : ℝ) :
    TimedDeformationRetract (𝟙 A) δ where
  r := 𝟙 A
  retract := by simp
  H := (TopCat.Homotopy.refl (𝟙 A)).cast rfl (by simp)
  fixed := fun _ _ ↦ rfl
  stationary := fun _ _ _ ↦ rfl

/-- The constant extension of a relative homotopy remains relative at all
real parameter values, including outside the unit interval. -/
theorem homotopy_extend_fixed {A B Z : TopCat.{u}} {i : A ⟶ B}
    {f g : B ⟶ Z} (H : TopCat.Homotopy f g)
    (hH : ∀ t a, H (t, i a) = f (i a)) (s : ℝ) (a : A) :
    H.extend s (i a) = f (i a) := by
  by_cases hs₀ : s ≤ 0
  · exact H.extend_apply_of_le_zero hs₀ _
  by_cases hs₁ : 1 ≤ s
  · rw [H.extend_apply_of_one_le hs₁]
    exact (H.map_one_left (i a)).symm.trans (hH 1 a)
  · rw [H.extend_apply_of_mem_I ⟨(not_le.mp hs₀).le, (not_le.mp hs₁).le⟩]
    exact hH _ _

/-- Add a deformation-retract stage during the first half of the preceding
stationary interval, without changing the preceding homotopy at all. -/
def TimedDeformationRetract.comp {A B C : TopCat.{u}} {i : A ⟶ B} {j : B ⟶ C}
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (h : TimedDeformationRetract i δ) (k : TopCat.CylinderStrongDeformationRetract j) :
    TimedDeformationRetract (i ≫ j) (δ / 2) := by
  let K : TopCat.Homotopy (𝟙 C) (k.r ≫ j) :=
    (TopCat.homotopyOfCylinder k.H k.H₀ k.H₁).symm
  have hK : ∀ t b, K (t, j b) = j b := by
    intro t b
    exact ConcreteCategory.congr_hom k.fixed (b, ULift.up (unitInterval.symm t))
  let Q : C(unitInterval × C, C) := {
    toFun := fun p ↦ if (p.1 : ℝ) ≤ δ then
      K.extend (2 * (p.1 : ℝ) / δ - 1) p.2 else j (h.H (p.1, k.r p.2))
    continuous_toFun := by
      apply continuous_if_le (by fun_prop) continuous_const
        (K.continuous.comp (by fun_prop)).continuousOn
        (j.hom.continuous.comp (h.H.continuous.comp (by fun_prop))).continuousOn
      intro p hp
      change K.extend (2 * (p.1 : ℝ) / δ - 1) p.2 = j (h.H (p.1, k.r p.2))
      rw [hp, show 2 * δ / δ - 1 = 1 by field_simp; ring,
        K.extend_one]
      exact congrArg j (h.stationary p.1 (k.r p.2) hp.le).symm }
  have hQ₀ : ∀ c, Q (0, c) = c := by
    intro c
    change (if (0 : ℝ) ≤ δ then K.extend (2 * 0 / δ - 1) c else _) = c
    rw [ite_eq_left hδ.le]
    exact K.extend_apply_of_le_zero (by norm_num) c
  have hQ₁ : ∀ c, Q (1, c) = (k.r ≫ h.r ≫ i ≫ j) c := by
    intro c
    change (if (1 : ℝ) ≤ δ then K.extend (2 * 1 / δ - 1) c
      else j (h.H (1, k.r c))) = _
    split_ifs with hδ₂
    · have hd : δ = 1 := le_antisymm hδ₁ hδ₂
      rw [show (2 : ℝ) * 1 / δ - 1 = 1 by norm_num [hd], K.extend_one]
      have hh := h.stationary 1 (k.r c) (by simp [hd])
      have hh₁ := h.H.map_one_left (k.r c)
      have hh₂ : (h.r ≫ i) (k.r c) = k.r c := hh₁.symm.trans hh
      exact congrArg j hh₂.symm
    · exact congrArg j (h.H.map_one_left (k.r c))
  refine ⟨k.r ≫ h.r, ?_, ⟨Q, hQ₀, hQ₁⟩, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc j k.r, k.retract]
    simpa using h.retract
  · intro t a
    change Q (t, j (i a)) = j (i a)
    change (if (t : ℝ) ≤ δ then K.extend (2 * (t : ℝ) / δ - 1) (j (i a))
      else j (h.H (t, k.r (j (i a))))) = j (i a)
    split_ifs with ht
    · exact homotopy_extend_fixed K hK _ _
    · have hr : k.r (j (i a)) = i a := ConcreteCategory.congr_hom k.retract (i a)
      rw [hr, h.fixed]
  · intro t c ht
    change Q (t, c) = c
    dsimp [Q]
    rw [ite_eq_left (by linarith : (t : ℝ) ≤ δ)]
    apply K.extend_apply_of_le_zero
    apply sub_nonpos.mpr
    exact (div_le_one hδ).mpr (by linarith)

/-- The new timed deformation restricts exactly to its predecessor. -/
theorem TimedDeformationRetract.comp_restrict
    {A B C : TopCat.{u}} {i : A ⟶ B} {j : B ⟶ C}
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (h : TimedDeformationRetract i δ) (k : TopCat.CylinderStrongDeformationRetract j)
    (t : unitInterval) (b : B) :
    (h.comp hδ hδ₁ k).H (t, j b) = j (h.H (t, b)) := by
  let K : TopCat.Homotopy (𝟙 C) (k.r ≫ j) :=
    (TopCat.homotopyOfCylinder k.H k.H₀ k.H₁).symm
  have hK : ∀ s a, K (s, j a) = j a := by
    intro s a
    exact ConcreteCategory.congr_hom k.fixed (a, ULift.up (unitInterval.symm s))
  change (if (t : ℝ) ≤ δ then K.extend (2 * (t : ℝ) / δ - 1) (j b)
    else j (h.H (t, k.r (j b)))) = j (h.H (t, b))
  split_ifs with ht
  · rw [homotopy_extend_fixed K hK, h.stationary t b ht]
    rfl
  · rw [show k.r (j b) = b from ConcreteCategory.congr_hom k.retract b]

/-- The actual composite from the initial term of a sequential diagram. -/
def sequentialInitialMap (F : ℕ ⥤ TopCat.{u}) : ∀ n, F.obj 0 ⟶ F.obj n
  | 0 => 𝟙 _
  | n + 1 => sequentialInitialMap F n ≫ F.map (homOfLE (Nat.le_succ n))

@[simp]
theorem sequentialInitialMap_eq (F : ℕ ⥤ TopCat.{u}) (n : ℕ) :
    sequentialInitialMap F n = F.map (homOfLE (Nat.zero_le n)) := by
  induction n with
  | zero => simp [sequentialInitialMap]
  | succ n ih =>
    rw [sequentialInitialMap, ih, ← F.map_comp]
    congr 1

/-- The length of the stationary part of the stagewise deformation. -/
def sequentialStationaryTime : ℕ → ℝ
  | 0 => 1
  | n + 1 => sequentialStationaryTime n / 2

theorem sequentialStationaryTime_pos (n : ℕ) : 0 < sequentialStationaryTime n := by
  induction n with
  | zero => norm_num [sequentialStationaryTime]
  | succ n ih => exact div_pos ih (by norm_num)

theorem sequentialStationaryTime_le_one (n : ℕ) : sequentialStationaryTime n ≤ 1 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => dsimp [sequentialStationaryTime]; linarith

/-- Recursively choose compatible timed deformations of all finite stages. -/
def sequentialTimedDeformation
    (F : ℕ ⥤ TopCat.{u})
    (h : ∀ n, TopCat.CylinderStrongDeformationRetract (F.map (homOfLE (Nat.le_succ n)))) :
    ∀ n, TimedDeformationRetract (sequentialInitialMap F n) (sequentialStationaryTime n)
  | 0 => TimedDeformationRetract.id (F.obj 0) 1
  | n + 1 => (sequentialTimedDeformation F h n).comp
      (sequentialStationaryTime_pos n) (sequentialStationaryTime_le_one n) (h n)

@[reassoc]
theorem sequentialTimedDeformation_retract_step
    (F : ℕ ⥤ TopCat.{u})
    (h : ∀ n, TopCat.CylinderStrongDeformationRetract (F.map (homOfLE (Nat.le_succ n))))
    (n : ℕ) : F.map (homOfLE (Nat.le_succ n)) ≫ (sequentialTimedDeformation F h (n + 1)).r =
      (sequentialTimedDeformation F h n).r := by
  change F.map (homOfLE (Nat.le_succ n)) ≫ (h n).r ≫ _ = _
  rw [← Category.assoc, (h n).retract, Category.id_comp]

theorem sequentialTimedDeformation_homotopy_step
    (F : ℕ ⥤ TopCat.{u})
    (h : ∀ n, TopCat.CylinderStrongDeformationRetract (F.map (homOfLE (Nat.le_succ n))))
    (n : ℕ) (t : unitInterval) (x : F.obj n) :
    (sequentialTimedDeformation F h (n + 1)).H
      (t, F.map (homOfLE (Nat.le_succ n)) x) =
    F.map (homOfLE (Nat.le_succ n)) ((sequentialTimedDeformation F h n).H (t, x)) :=
  TimedDeformationRetract.comp_restrict _ _ _ _ _ _

/-- Compatible consecutive components are a cocone on a sequential diagram. -/
def sequentialCocone {F : ℕ ⥤ TopCat.{u}} {Z : TopCat.{u}}
    (f : ∀ n, F.obj n ⟶ Z)
    (hf : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ f (n + 1) = f n) : Cocone F := by
  have hcompat {n m : ℕ} (h : n ≤ m) : F.map (homOfLE h) ≫ f m = f n := by
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih =>
      have hsplit : (homOfLE (Nat.le.step h) : n ⟶ m + 1) =
          homOfLE h ≫ homOfLE (Nat.le_succ m) := Subsingleton.elim _ _
      rw [hsplit, F.map_comp, Category.assoc, hf, ih]
  exact {
    pt := Z
    ι := {
      app := f
      naturality := fun n m a ↦ by
        have ha : homOfLE (leOfHom a) = a := Subsingleton.elim _ _
        change F.map a ≫ f m = f n ≫ 𝟙 Z
        simpa only [Category.comp_id, ha] using hcompat (leOfHom a) } }

/-- Sequential composites of actual strong deformation retractions are
actual strong deformation retractions. No coherence of the given
stagewise deformations is assumed. -/
def sequentialStrongDeformationRetract
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ n, TopCat.CylinderStrongDeformationRetract (F.map (homOfLE (Nat.le_succ n)))) :
    TopCat.CylinderStrongDeformationRetract (c.ι.app 0) := by
  let T := sequentialTimedDeformation F h
  let d := sequentialCocone (fun n ↦ (T n).r)
    (sequentialTimedDeformation_retract_step F h)
  let r : c.pt ⟶ F.obj 0 := hc.desc d
  have hr (n : ℕ) : c.ι.app n ≫ r = (T n).r := hc.fac d n
  have hinit (n : ℕ) : sequentialInitialMap F n ≫ c.ι.app n = c.ι.app 0 := by
    rw [sequentialInitialMap_eq]
    exact c.w _
  let Hn (n : ℕ) : F.obj n ⊗ TopCat.I ⟶ c.pt := (T n).H.h ≫ c.ι.app n
  have hHstep (n : ℕ) :
      (F.map (homOfLE (Nat.le_succ n)) ▷ TopCat.I) ≫ Hn (n + 1) = Hn n := by
    ext ⟨x, t⟩
    change c.ι.app (n + 1) ((T (n + 1)).H
      (t.down, F.map (homOfLE (Nat.le_succ n)) x)) =
      c.ι.app n ((T n).H (t.down, x))
    rw [sequentialTimedDeformation_homotopy_step]
    exact ConcreteCategory.congr_hom (c.w (homOfLE (Nat.le_succ n))) _
  let e : Cocone (F ⋙ tensorRight TopCat.I) := sequentialCocone Hn hHstep
  let hcI := isColimitOfPreserves (tensorRight TopCat.I) hc
  let H : c.pt ⊗ TopCat.I ⟶ c.pt := hcI.desc e
  have hH (n : ℕ) : (c.ι.app n ▷ TopCat.I) ≫ H = Hn n := hcI.fac e n
  have hH₀ : TopCat.ι₀ ≫ H = 𝟙 c.pt := by
    apply hc.hom_ext
    intro n
    rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hH]
    dsimp [Hn]
    rw [← Category.assoc, (T n).H.ι₀_h]
    simp
  have hH₁ : TopCat.ι₁ ≫ H = r ≫ c.ι.app 0 := by
    apply hc.hom_ext
    intro n
    rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hH]
    dsimp [Hn]
    rw [← Category.assoc, (T n).H.ι₁_h, Category.assoc, hinit,
      ← Category.assoc, hr]
  let K : TopCat.Homotopy (r ≫ c.ι.app 0) (𝟙 c.pt) :=
    (TopCat.homotopyOfCylinder H hH₀ hH₁).symm
  refine ⟨r, hr 0, K.h, K.ι₀_h, K.ι₁_h, ?_⟩
  ext ⟨x, t⟩
  change H (c.ι.app 0 x, ULift.up (unitInterval.symm t.down)) = c.ι.app 0 x
  have he := ConcreteCategory.congr_hom (hH 0)
    (x, ULift.up (unitInterval.symm t.down))
  exact he

/-- A sequential composite of homotopy-equivalence cofibrations is a
homotopy equivalence, with the actual initial colimit map as forward map. -/
def sequentialHomotopyEquivOfCofibrations
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, TopCat.HomotopyExtensionProperty (F.map (homOfLE (Nat.le_succ n))))
    (eF : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (F.obj (n + 1)))
    (heF : ∀ n, (eF n).toFun = (F.map (homOfLE (Nat.le_succ n))).hom) :
    ContinuousMap.HomotopyEquiv (F.obj 0) c.pt :=
  (sequentialStrongDeformationRetract F c hc fun n ↦
    (TopCat.homotopyExtensionProperty_strongDeformationRetract (hF n) (eF n) (heF
      n)).some).toHomotopyEquiv

@[simp]
theorem sequentialHomotopyEquivOfCofibrations_toFun
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, TopCat.HomotopyExtensionProperty (F.map (homOfLE (Nat.le_succ n))))
    (eF : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (F.obj (n + 1)))
    (heF : ∀ n, (eF n).toFun = (F.map (homOfLE (Nat.le_succ n))).hom) :
    (sequentialHomotopyEquivOfCofibrations F c hc hF eF heF).toFun =
      (c.ι.app 0).hom := rfl

end TopCat
