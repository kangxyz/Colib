/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.Bisimplicial.LatchingIntersections
public import Colib.Topology.Realization.MapEquivalence

/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/BisimplicialLatchingEquivalences.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native simplicial objects,
realization maps and full proof are retained. -/

/-!
# Row equivalences induce latching realization equivalences -/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.BisimplicialRealization
variable {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)

/-- The comparison on a degeneracy attachment's lower-dimensional boundary. -/
def lowerLatchingMap (n k : ℕ) :
    (lowerLatching X n k : SSet.{u}) ⟶ (lowerLatching Y n k : SSet.{u}) := by
  cases n with
  | zero => exact SSet.Subcomplex.isInitialBot.to _
  | succ n => exact partialLatchingMap η n k

@[reassoc (attr := simp)] lemma lowerLatchingMap_ι (n k : ℕ) :
    lowerLatchingMap η n k ≫ (lowerLatching Y n k).ι =
      (lowerLatching X n k).ι ≫ η.app (op ⦋n⦌) := by
  cases n with
  | zero => apply SSet.Subcomplex.isInitialBot.hom_ext
  | succ n => rfl

lemma latchingFace_naturality (n k : ℕ) (hk : k < n + 1) :
    latchingFace X n k hk ≫ partialLatchingMap η n k =
      lowerLatchingMap η n k ≫ latchingFace Y n k hk := by
  apply (cancel_mono (partialLatching Y n k).ι).1
  rw [Category.assoc, partialLatchingMap_ι, ← Category.assoc, latchingFace_ι,
    Category.assoc, SimplicialObject.σ_naturality, ← Category.assoc,
    ← lowerLatchingMap_ι, Category.assoc, Category.assoc, latchingFace_ι]

lemma latchingCell_naturality (n k : ℕ) (hk : k < n + 1) :
    latchingCell X n k hk ≫ partialLatchingMap η n (k + 1) =
      η.app (op ⦋n⦌) ≫ latchingCell Y n k hk := by
  apply (cancel_mono (partialLatching Y n (k + 1)).ι).1
  rw [Category.assoc, partialLatchingMap_ι, ← Category.assoc, latchingCell_ι,
    Category.assoc, latchingCell_ι]
  exact SimplicialObject.σ_naturality η ⟨k, hk⟩

lemma partialLatching_inclusion_naturality (n k : ℕ) :
    SSet.Subcomplex.homOfLE (partialLatching_mono X n (Nat.le_succ k)) ≫
      partialLatchingMap η n (k + 1) =
      partialLatchingMap η n k ≫
        SSet.Subcomplex.homOfLE (partialLatching_mono Y n (Nat.le_succ k)) := rfl

/-- Initiality of the zero-stage partial latching simplicial set, transported from the bottom
subcomplex. -/
-- Preserve the public zero-stage initiality witness name for existing downstream references.
def partialLatchingZeroIsInitial (X : SimplicialObject SSet.{u}) (n : ℕ) :
    IsInitial (partialLatching X n 0 : SSet.{u}) :=
  SSet.Subcomplex.isInitialBot.ofIso (SSet.Subcomplex.eqToIso (partialLatching_zero X n)).symm

/-- Every partial latching comparison is a realization equivalence. The
induction uses genuine degeneracy-union pushouts and mono HEP. -/
theorem partialLatchingMap_isRealizationEquivalence
    (h : ∀ n, IsRealizationEquivalence (η.app (op ⦋n⦌))) :
    ∀ n k, k ≤ n + 1 → IsRealizationEquivalence (partialLatchingMap η n k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro k
    induction k with
    | zero =>
      intro _
      exact IsRealizationEquivalence.of_isInitial _
        (partialLatchingZeroIsInitial X n) (partialLatchingZeroIsInitial Y n)
    | succ k ihk =>
      intro hk
      have hk' : k < n + 1 := by omega
      have hlower : IsRealizationEquivalence (lowerLatchingMap η n k) := by
        cases n with
        | zero =>
          exact IsRealizationEquivalence.of_isInitial _
            SSet.Subcomplex.isInitialBot SSet.Subcomplex.isInitialBot
        | succ m => exact ihn m (by omega) k (by omega)
      exact IsRealizationEquivalence.pushout
        (partialLatching_isPushout X n k hk').flip (partialLatching_isPushout Y n k hk').flip
        (lowerLatchingMap η n k) (η.app (op ⦋n⦌)) (partialLatchingMap η n k)
        (partialLatchingMap η n (k + 1))
        (lowerLatchingMap_ι η n k).symm (latchingFace_naturality η n k hk')
        (latchingCell_naturality η n k hk') (partialLatching_inclusion_naturality η n k)
        hlower (h n) (ihk (by omega))

/-- Full outer latching objects inherit every rowwise realization equivalence. -/
theorem latchingMap_isRealizationEquivalence
    (h : ∀ n, IsRealizationEquivalence (η.app (op ⦋n⦌))) (n : ℕ) :
    IsRealizationEquivalence (latchingMap η n) := by
  cases n with
  | zero =>
    exact IsRealizationEquivalence.of_isInitial _
      SSet.Subcomplex.isInitialBot SSet.Subcomplex.isInitialBot
  | succ n => exact partialLatchingMap_isRealizationEquivalence η h n (n + 1) le_rfl

end SSet.BisimplicialRealization
