/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.ThreeSideSquare

/-! # Parameterized descent through the compact three-sided square

Continuous families constant along both collapsed sides descend after product with any space.
The proper parameter quotient establishes joint continuity without local compactness of that space.
-/
/-! Implementation source: `Quillen/Topology/Homotopy/ThreeSideSquareLift.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, coordinates,
whole boundary traces and universe parameters are retained with native owners.
-/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
namespace Topology.ThreeSideSquare
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (J : C((unitInterval × unitInterval) × X, Y))
  (h₀ : ∀ (r : unitInterval) (x : X), J ((r, 0), x) = J ((0, 0), x))
  (h₁ : ∀ (r : unitInterval) (x : X), J ((r, 1), x) = J ((0, 1), x))

include h₀ h₁
private lemma eq_of_collapse_eq {a b : unitInterval × unitInterval}
    (h : collapse a = collapse b) (x : X) : J (a, x) = J (b, x) := by
  rcases collapse_fiber h with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [h]
  · rcases a with ⟨r, s⟩
    rcases b with ⟨r', s'⟩
    dsimp only at ha hb
    subst s
    subst s'
    exact (h₀ r x).trans (h₀ r' x).symm
  · rcases a with ⟨r, s⟩
    rcases b with ⟨r', s'⟩
    dsimp only at ha hb
    subst s
    subst s'
    exact (h₁ r x).trans (h₁ r' x).symm

/-- The actual jointly continuous family descended through the proper parameter quotient. -/
def liftFamily : C((unitInterval × unitInterval) × X, Y) where
  toFun z := J (Function.surjInv collapse_surjective z.1, z.2)
  continuous_toFun := (isQuotientMap_collapse_prod X).continuous_iff.mpr (by
    change Continuous (fun z : (unitInterval × unitInterval) × X =>
      J (Function.surjInv collapse_surjective (collapse z.1), z.2))
    have he : (fun z : (unitInterval × unitInterval) × X =>
        J (Function.surjInv collapse_surjective (collapse z.1), z.2)) = J := by
      funext z
      exact eq_of_collapse_eq J h₀ h₁ (Function.surjInv_eq _ _) z.2
    rw [he]
    exact J.continuous)

/-- Descent retains the whole original parameter family, rather than only its boundary. -/
lemma liftFamily_collapse (z : unitInterval × unitInterval) (x : X) :
    liftFamily J h₀ h₁ (collapse z, x) = J (z, x) :=
  eq_of_collapse_eq J h₀ h₁ (Function.surjInv_eq _ _) x

/-- The unchanged lower boundary of the original family is preserved literally. -/
lemma liftFamily_zero (s : unitInterval) (x : X) :
    liftFamily J h₀ h₁ ((0, s), x) = J ((0, s), x) := by
  simpa only [collapse_zero] using liftFamily_collapse J h₀ h₁ (0, s) x

/-- The target left edge is the first quarter of the original upper edge. -/
lemma liftFamily_left (r : unitInterval) (x : X) :
    liftFamily J h₀ h₁ ((r, 0), x) = J ((1, leftTime r), x) := by
  simpa only [collapse_leftTime] using liftFamily_collapse J h₀ h₁ (1, leftTime r) x

/-- The target upper edge is the next quarter of the original upper edge. -/
lemma liftFamily_top (s : unitInterval) (x : X) :
    liftFamily J h₀ h₁ ((1, s), x) = J ((1, topTime s), x) := by
  simpa only [collapse_topTime] using liftFamily_collapse J h₀ h₁ (1, topTime s) x

/-- The target right edge is the final half of the original upper edge in reverse direction. -/
lemma liftFamily_right (r : unitInterval) (x : X) :
    liftFamily J h₀ h₁ ((r, 1), x) = J ((1, rightTime r), x) := by
  simpa only [collapse_rightTime] using liftFamily_collapse J h₀ h₁ (1, rightTime r) x

/-- The original parameterized quotient equation uniquely determines the descended family. -/
lemma liftFamily_unique (K : C((unitInterval × unitInterval) × X, Y))
    (hK : ∀ z x, K (collapse z, x) = J (z, x)) : K = liftFamily J h₀ h₁ := by
  ext ⟨z, x⟩
  obtain ⟨z, rfl⟩ := collapse_surjective z
  exact (hK z x).trans (liftFamily_collapse J h₀ h₁ z x).symm

end Topology.ThreeSideSquare
