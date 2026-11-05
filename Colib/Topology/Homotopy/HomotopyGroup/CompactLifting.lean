/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.Nullhomotopy

/-! # Actual homotopy-group bijections from injective compact-source lifting

An injective continuous map that admits exact lifts of compact-source maps
induces bijections of the genuine homotopy sets. Injectivity forces every
lifted cube boundary and both endpoints of every lifted relative homotopy
to retain the original chosen values. No fiber or weak-equivalence conclusion
is included in the lifting hypothesis.
-/
/-! Source: `Quillen/Topology/HomotopyGroups/CompactLifting.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universes are retained.
The S-product isomorphism is not a normalized or strict S-model comparison. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval

namespace Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Exact continuous lifting for ordinary small compact source spaces.
These include all finite cubes and their actual homotopy cylinders. -/
def HasCompactSourceLifts (e : C(X, Y)) : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [CompactSpace T] (f : C(T, Y)),
    ∃ g : C(T, X), e.comp g = f

/-- Genuine finite-dimensional homotopy-set bijectivity follows from actual
compact lifts and injectivity of the prescribed forward continuous map. -/
theorem homotopyGroupMap_bijective_of_compact_lifts
    (e : C(X, Y)) (he : Function.Injective e) (hl : HasCompactSourceLifts e)
    (x : X) (n : ℕ) : Function.Bijective (HomotopyGroup.map (N := Fin n) e (x := x) rfl) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | h p =>
      induction b using Quotient.inductionOn with | h q =>
        obtain ⟨H⟩ := Quotient.exact hab
        obtain ⟨G, hG⟩ := hl _ H.toContinuousMap
        let H' : p.val.HomotopyRel q.val (Cube.boundary (Fin n)) := {
          toHomotopy := {
            toContinuousMap := G
            map_zero_left t := he ((DFunLike.congr_fun hG (0, t)).trans (H.apply_zero t))
            map_one_left t := he ((DFunLike.congr_fun hG (1, t)).trans (H.apply_one t)) }
          prop' s t ht := he ((DFunLike.congr_fun hG (s, t)).trans (H.eq_fst s ht)) }
        exact Quotient.sound ⟨H'⟩
  · intro a
    induction a using Quotient.inductionOn with | h p =>
      obtain ⟨g, hg⟩ := hl _ p.val
      let q : GenLoop (Fin n) X x := ⟨g, fun t ht ↦
        he ((DFunLike.congr_fun hg t).trans (GenLoop.boundary p t ht))⟩
      refine ⟨Quotient.mk' q, ?_⟩
      apply congrArg Quotient.mk'
      exact GenLoop.ext _ _ (fun t ↦ DFunLike.congr_fun hg t)

/-- Positive-dimensional group bijectivity retains any displayed equality
of the actual forward image of the basepoint. -/
theorem piMap_bijective_of_compact_lifts
    (e : C(X, Y)) (he : Function.Injective e) (hl : HasCompactSourceLifts e)
    {x : X} {y : Y} (hp : e x = y) (n : ℕ) : Function.Bijective (HomotopyGroup.piMap n e hp) := by
  subst y
  exact homotopyGroupMap_bijective_of_compact_lifts e he hl x (n + 1)

/-- The resulting group equivalence has exactly the original based map as
its forward homomorphism. -/
def piEquivOfCompactLifts
    (e : C(X, Y)) (he : Function.Injective e) (hl : HasCompactSourceLifts e)
    {x : X} {y : Y} (hp : e x = y) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X x ≃* HomotopyGroup.Pi (n + 1) Y y :=
  MulEquiv.ofBijective (HomotopyGroup.piMap n e hp) (piMap_bijective_of_compact_lifts e he hl hp n)

/-- The forward homomorphism is the original based map. -/
@[simp] theorem piEquivOfCompactLifts_coe
    (e : C(X, Y)) (he : Function.Injective e) (hl : HasCompactSourceLifts e)
    {x : X} {y : Y} (hp : e x = y) (n : ℕ) :
    (piEquivOfCompactLifts e he hl hp n : _ →* _) = HomotopyGroup.piMap n e hp := rfl

end Topology
