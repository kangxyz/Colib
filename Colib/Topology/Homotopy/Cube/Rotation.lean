/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
A genuine identity-to-quarter-turn homotopy of the unit square. Sup-norm radial normalization proves
continuity even at the center. Every time preserves the full boundary set; boundary points are not
asserted to be fixed individually.
-/
/-! Implementation source: `Quillen/Topology/Cube/Rotation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section


noncomputable section
open Filter
open scoped Topology unitInterval
namespace Topology

/-- The linear interpolation from the identity to a quarter-turn of the real plane. -/
def quarterTurnLinear (s : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1-s)*v.1-s*v.2, s*v.1+(1-s)*v.2)

lemma quarterTurnLinear_eq_zero_iff (s : ℝ) (v : ℝ × ℝ) :
    quarterTurnLinear s v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    change (1-s)*v.1-s*v.2=0 at hx
    change s*v.1+(1-s)*v.2=0 at hy
    have hd : 0 < (1-s)^2+s^2 := by nlinarith [sq_nonneg (s-1/2)]
    have h1 : ((1-s)^2+s^2)*v.1=0 := by linear_combination (1-s)*hx+s*hy
    have h2 : ((1-s)^2+s^2)*v.2=0 := by linear_combination (-s)*hx+(1-s)*hy
    exact Prod.ext ((mul_eq_zero.mp h1).resolve_left (ne_of_gt hd))
      ((mul_eq_zero.mp h2).resolve_left (ne_of_gt hd))
  · rintro rfl
    simp [quarterTurnLinear]

lemma continuous_quarterTurnLinear : Continuous (fun p : ℝ × (ℝ × ℝ) ↦ quarterTurnLinear p.1 p.2) :=
  by
  unfold quarterTurnLinear
  fun_prop

/-- Normalize the actual nonsingular linear rotation by the sup-norm radius. -/
def squareRadialRotation (s : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (‖v‖ / ‖quarterTurnLinear s v‖) • quarterTurnLinear s v

lemma squareRadialRotation_zero (s : ℝ) : squareRadialRotation s 0 = 0 := by
  simp [squareRadialRotation, quarterTurnLinear]

lemma norm_squareRadialRotation (s : ℝ) (v : ℝ × ℝ) :
    ‖squareRadialRotation s v‖ = ‖v‖ := by
  by_cases hv : v=0
  · simp [hv, squareRadialRotation_zero]
  · have hn : ‖quarterTurnLinear s v‖ ≠ 0 := norm_ne_zero_iff.mpr
      (fun h ↦ hv ((quarterTurnLinear_eq_zero_iff s v).mp h))
    rw [squareRadialRotation, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact div_mul_cancel₀ _ hn

lemma continuous_squareRadialRotation :
    Continuous (fun p : ℝ × (ℝ × ℝ) ↦ squareRadialRotation p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.2=0
  · change Tendsto (fun q : ℝ × (ℝ × ℝ) ↦ squareRadialRotation q.1 q.2) (𝓝 p)
      (𝓝 (squareRadialRotation p.1 p.2))
    rw [hp, squareRadialRotation_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht : Tendsto (fun q : ℝ × (ℝ × ℝ) ↦ ‖q.2‖) (𝓝 p) (𝓝 ‖p.2‖) :=
      continuous_snd.norm.continuousAt
    simpa only [norm_squareRadialRotation, hp, norm_zero] using ht
  · change ContinuousAt (fun q : ℝ × (ℝ × ℝ) ↦
      (‖q.2‖ / ‖quarterTurnLinear q.1 q.2‖) • quarterTurnLinear q.1 q.2) p
    exact (continuous_snd.norm.continuousAt.div continuous_quarterTurnLinear.norm.continuousAt
      (norm_ne_zero_iff.mpr (fun h ↦ hp ((quarterTurnLinear_eq_zero_iff _ _).mp h)))).smul
        continuous_quarterTurnLinear.continuousAt

lemma squareRadialRotation_at_zero (v : ℝ × ℝ) : squareRadialRotation 0 v = v := by
  have h : quarterTurnLinear 0 v = v := by ext <;> simp [quarterTurnLinear]
  by_cases hv : v=0
  · simp [hv, squareRadialRotation_zero]
  · simp [squareRadialRotation,h,div_self (norm_ne_zero_iff.mpr hv)]

lemma squareRadialRotation_at_one (v : ℝ × ℝ) : squareRadialRotation 1 v = (-v.2,v.1) := by
  have h : quarterTurnLinear 1 v = (-v.2,v.1) := by ext <;> simp [quarterTurnLinear]
  have hn : ‖(-v.2,v.1)‖ = ‖v‖ := by simp only [Prod.norm_def, norm_neg]; exact max_comm _ _
  by_cases hv : v=0
  · simp [hv, squareRadialRotation_zero]
    rfl
  · simp [squareRadialRotation,h,hn,div_self (norm_ne_zero_iff.mpr hv)]

end Topology

end


noncomputable section
open scoped Topology unitInterval
namespace Topology

/-- Centered real coordinates on the unit square. -/
def squareCenter (x : unitInterval × unitInterval) : ℝ × ℝ :=
  (2*(x.1:ℝ)-1,2*(x.2:ℝ)-1)

lemma continuous_squareCenter : Continuous squareCenter := by unfold squareCenter; fun_prop

lemma squareCenter_norm_le (x : unitInterval × unitInterval) : ‖squareCenter x‖ ≤ 1 := by
  change max |2*(x.1:ℝ)-1| |2*(x.2:ℝ)-1| ≤ 1
  apply max_le <;> apply abs_le.mpr
  · constructor <;> nlinarith [x.1.property.1,x.1.property.2]
  · constructor <;> nlinarith [x.2.property.1,x.2.property.2]

/-- Membership in one of the four boundary edges of the unit square. -/
def SquareBoundary (x : unitInterval × unitInterval) : Prop :=
  x.1=0 ∨ x.1=1 ∨ x.2=0 ∨ x.2=1

lemma squareBoundary_iff_norm (x : unitInterval × unitInterval) :
    SquareBoundary x ↔ ‖squareCenter x‖=1 := by
  constructor
  · intro h
    apply le_antisymm (squareCenter_norm_le x)
    rcases h with h|h|h|h
    · have hn : ‖(squareCenter x).1‖=1 := by norm_num [squareCenter,h]
      simpa only [hn] using norm_fst_le (squareCenter x)
    · have hn : ‖(squareCenter x).1‖=1 := by norm_num [squareCenter,h]
      simpa only [hn] using norm_fst_le (squareCenter x)
    · have hn : ‖(squareCenter x).2‖=1 := by norm_num [squareCenter,h]
      simpa only [hn] using norm_snd_le (squareCenter x)
    · have hn : ‖(squareCenter x).2‖=1 := by norm_num [squareCenter,h]
      simpa only [hn] using norm_snd_le (squareCenter x)
  · intro hn
    by_contra h
    unfold SquareBoundary at h
    push Not at h
    rcases h with ⟨h00,h01,h10,h11⟩
    have ha0 : (x.1:ℝ) ≠ 0 := fun e ↦ h00 (Subtype.ext e)
    have ha1 : (x.1:ℝ) ≠ 1 := fun e ↦ h01 (Subtype.ext e)
    have hb0 : (x.2:ℝ) ≠ 0 := fun e ↦ h10 (Subtype.ext e)
    have hb1 : (x.2:ℝ) ≠ 1 := fun e ↦ h11 (Subtype.ext e)
    have hapos : 0 < (x.1:ℝ) := lt_of_le_of_ne x.1.property.1 (Ne.symm ha0)
    have halt : (x.1:ℝ) < 1 := lt_of_le_of_ne x.1.property.2 ha1
    have hbpos : 0 < (x.2:ℝ) := lt_of_le_of_ne x.2.property.1 (Ne.symm hb0)
    have hblt : (x.2:ℝ) < 1 := lt_of_le_of_ne x.2.property.2 hb1
    have ha : |2*(x.1:ℝ)-1|<1 := abs_lt.mpr ⟨by nlinarith [x.1.property.1],by nlinarith
      [x.1.property.2]⟩
    have hb : |2*(x.2:ℝ)-1|<1 := abs_lt.mpr ⟨by nlinarith [x.2.property.1],by nlinarith
      [x.2.property.2]⟩
    have hl : ‖squareCenter x‖<1 := max_lt ha hb
    exact (ne_of_lt hl) hn

/-- Recenter a point of the closed sup-norm unit ball into the original square. -/
def squareUncenter (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) : unitInterval × unitInterval :=
  (⟨(v.1+1)/2,by
      have h : |v.1|≤1 := (norm_fst_le v).trans hv
      obtain ⟨h0,h1⟩ := abs_le.mp h
      constructor <;> linarith⟩,
   ⟨(v.2+1)/2,by
      have h : |v.2|≤1 := (norm_snd_le v).trans hv
      obtain ⟨h0,h1⟩ := abs_le.mp h
      constructor <;> linarith⟩)

lemma squareCenter_uncenter (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) :
    squareCenter (squareUncenter v hv) = v := by
  ext <;> dsimp [squareCenter,squareUncenter] <;> ring

lemma squareUncenter_center (x : unitInterval × unitInterval) :
    squareUncenter (squareCenter x) (squareCenter_norm_le x) = x := by
  apply Prod.ext <;> apply Subtype.ext <;> dsimp [squareUncenter,squareCenter] <;> ring

/-- The actual radius-preserving rotation of the original unit square. -/
def squareRotationFun (s : unitInterval) (x : unitInterval × unitInterval) :
    unitInterval × unitInterval :=
  squareUncenter (squareRadialRotation s (squareCenter x))
    ((norm_squareRadialRotation s (squareCenter x)).le.trans (squareCenter_norm_le x))

lemma continuous_squareRotationFun :
    Continuous (fun z : unitInterval × (unitInterval × unitInterval) ↦ squareRotationFun z.1 z.2) :=
      by
  have h : Continuous (fun z : unitInterval × (unitInterval × unitInterval) ↦
      squareRadialRotation z.1 (squareCenter z.2)) :=
    continuous_squareRadialRotation.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_squareCenter.comp
        continuous_snd))
  exact (((h.fst.add continuous_const).div_const 2).subtype_mk _).prodMk
    (((h.snd.add continuous_const).div_const 2).subtype_mk _)

lemma squareRotationFun_zero (x : unitInterval × unitInterval) : squareRotationFun 0 x = x := by
  unfold squareRotationFun
  change squareUncenter (squareRadialRotation 0 (squareCenter x)) _ = x
  simp only [squareRadialRotation_at_zero]
  exact squareUncenter_center x

lemma squareRotationFun_one (x : unitInterval × unitInterval) :
    squareRotationFun 1 x = (unitInterval.symm x.2,x.1) := by
  apply Prod.ext <;> apply Subtype.ext
  · change ((squareRadialRotation 1 (squareCenter x)).1+1)/2 = 1-(x.2:ℝ)
    rw [squareRadialRotation_at_one]
    dsimp [squareCenter]
    ring
  · change ((squareRadialRotation 1 (squareCenter x)).2+1)/2 = (x.1:ℝ)
    rw [squareRadialRotation_at_one]
    dsimp [squareCenter]
    ring

lemma squareRotationFun_boundary (s : unitInterval) (x : unitInterval × unitInterval)
    (hx : SquareBoundary x) : SquareBoundary (squareRotationFun s x) := by
  apply (squareBoundary_iff_norm _).mpr
  rw [squareRotationFun,squareCenter_uncenter,norm_squareRadialRotation]
  exact (squareBoundary_iff_norm x).mp hx

/-- A genuine homotopy from identity to quarter-turn; each time preserves the
four-edge boundary set, rather than fixing each boundary point separately. -/
def squareRotationHomotopy : (ContinuousMap.id (unitInterval × unitInterval)).Homotopy
    ⟨fun x ↦ (unitInterval.symm x.2,x.1),by fun_prop⟩ where
  toFun z := squareRotationFun z.1 z.2
  continuous_toFun := continuous_squareRotationFun
  map_zero_left := squareRotationFun_zero
  map_one_left := squareRotationFun_one

lemma squareRotationHomotopy_boundary (s : unitInterval) (x : unitInterval × unitInterval)
    (hx : SquareBoundary x) : SquareBoundary (squareRotationHomotopy (s,x)) :=
  squareRotationFun_boundary s x hx

end Topology
