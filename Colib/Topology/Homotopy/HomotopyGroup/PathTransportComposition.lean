/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportHomotopy
/-!
Implementation provenance:
`Quillen/Topology/HomotopyGroups/PathTransportComposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Composition of the original all-degree basepoint transports -/
@[expose] public section
noncomputable section
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x y z : X}

/-- Concatenating the specified paths composes their original transports. -/
theorem pathTransport_trans (p : Path x y) (q : Path y z) (n : ℕ)
    (a : HomotopyGroup.Pi n X x) :
    pathTransport (p.trans q) n a = pathTransport q n (pathTransport p n a) := by
  let H : C(unitInterval × unitInterval, X) :=
    ⟨fun st => (p.trans q).extend ((st.2 : ℝ) * (1 + (st.1 : ℝ)) / 2), by fun_prop⟩
  have h₀ : ∀ t, H (0, t) = p t := by
    intro t
    change (p.trans q).extend ((t : ℝ) * (1 + 0) / 2) = p t
    rw [add_zero, mul_one,
      Path.extend_trans_of_le_half p q (by linarith [t.property.2])]
    rw [show 2 * ((t : ℝ) / 2) = t by ring]
    exact Path.extend_apply p t.property
  have h₁ : ∀ t, H (1, t) = (p.trans q) t := by
    intro t
    change (p.trans q).extend ((t : ℝ) * (1 + 1) / 2) = (p.trans q) t
    rw [show (t : ℝ) * (1 + 1) / 2 = t by ring]
    exact Path.extend_apply (p.trans q) t.property
  have hl : ∀ t, H (t, 0) = (Path.refl x) t := by
    intro t
    simp [H]
  have hr : ∀ t, H (t, 1) = q t := by
    intro t
    change (p.trans q).extend (1 * (1 + (t : ℝ)) / 2) = q t
    rw [one_mul,
      Path.extend_trans_of_half_le p q (by linarith [t.property.1])]
    rw [show 2 * ((1 + (t : ℝ)) / 2) - 1 = t by ring]
    exact Path.extend_apply q t.property
  simpa only [pathTransport_refl, Equiv.refl_apply] using
    pathTransport_square p (p.trans q) (Path.refl x) q H h₀ h₁ hl hr n a
end Topology
