/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.Nullhomotopy

/-! # Actual based homotopy groups of a topological product

The forward homomorphism is the pair of the original projection maps.
Bijectivity is proved on actual generalized loops and relative homotopies,
without a commutativity hypothesis or a chosen homotopy equivalence.
-/
/-! Source: `Quillen/Topology/HomotopyGroups/Product.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universes are retained.
The S-product isomorphism is not a normalized or strict S-model comparison. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval

namespace Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pair the actual based homotopy-group maps of the two projections. -/
def piProdMap (n : ℕ) (x : X) (y : Y) :
    HomotopyGroup.Pi (n + 1) (X × Y) (x, y) →*
      HomotopyGroup.Pi (n + 1) X x × HomotopyGroup.Pi (n + 1) Y y :=
  (HomotopyGroup.piMap n ContinuousMap.fst rfl).prod (HomotopyGroup.piMap n ContinuousMap.snd rfl)

/-- Projection of actual generalized loops is bijective on homotopy classes:
loops pair pointwise, and their two relative homotopies pair pointwise. -/
theorem piProdMap_bijective (n : ℕ) (x : X) (y : Y) : Function.Bijective (piProdMap n x y) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | h p =>
      induction b using Quotient.inductionOn with | h q =>
        have h₁ := congrArg _root_.Prod.fst hab
        have h₂ := congrArg _root_.Prod.snd hab
        change Quotient.mk' (GenLoop.postcomp ContinuousMap.fst rfl p) =
          Quotient.mk' (GenLoop.postcomp ContinuousMap.fst rfl q) at h₁
        change Quotient.mk' (GenLoop.postcomp ContinuousMap.snd rfl p) =
          Quotient.mk' (GenLoop.postcomp ContinuousMap.snd rfl q) at h₂
        obtain ⟨H₁⟩ := Quotient.exact h₁
        obtain ⟨H₂⟩ := Quotient.exact h₂
        let H : p.val.HomotopyRel q.val (Cube.boundary (Fin (n + 1))) := {
          toHomotopy := H₁.toHomotopy.prodMk H₂.toHomotopy
          prop' t z hz := _root_.Prod.ext (H₁.eq_fst t hz) (H₂.eq_fst t hz) }
        exact Quotient.sound ⟨H⟩
  · rintro ⟨a, b⟩
    induction a using Quotient.inductionOn with | h p =>
      induction b using Quotient.inductionOn with | h q =>
        let r : GenLoop (Fin (n + 1)) (X × Y) (x, y) :=
          ⟨p.val.prodMk q.val, fun t ht ↦ _root_.Prod.ext
            (GenLoop.boundary p t ht) (GenLoop.boundary q t ht)⟩
        refine ⟨Quotient.mk' r, ?_⟩
        apply _root_.Prod.ext
        · apply congrArg Quotient.mk'
          ext t
          rfl
        · apply congrArg Quotient.mk'
          ext t
          rfl

/-- The actual product equivalence, retaining projection as its forward map. -/
def piProdEquiv (n : ℕ) (x : X) (y : Y) :
    HomotopyGroup.Pi (n + 1) (X × Y) (x, y) ≃*
      HomotopyGroup.Pi (n + 1) X x × HomotopyGroup.Pi (n + 1) Y y :=
  MulEquiv.ofBijective (piProdMap n x y) (piProdMap_bijective n x y)

/-- The forward homomorphism consists of the two projection maps. -/
@[simp] theorem piProdEquiv_coe (n : ℕ) (x : X) (y : Y) :
    (piProdEquiv n x y : HomotopyGroup.Pi (n + 1) (X × Y) (x, y) →*
      HomotopyGroup.Pi (n + 1) X x × HomotopyGroup.Pi (n + 1) Y y) =
      (HomotopyGroup.piMap n ContinuousMap.fst rfl).prod (HomotopyGroup.piMap n
        ContinuousMap.snd rfl) := rfl

end Topology
