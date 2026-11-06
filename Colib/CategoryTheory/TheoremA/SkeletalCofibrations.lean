/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.BisimplicialCoproducts
public import Colib.CategoryTheory.TheoremA.EnrichedBoundaryHEP

/-! Source: Quillen/CategoryTheory/TheoremA/SkeletalCofibrations.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-! # Genuine cofibrations in the realized base-skeleton tower -/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u

namespace CategoryTheory.TheoremA

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The realized coproduct of all enriched simplex-boundary inclusions has HEP. -/
theorem homotopyExtensionProperty_replacementCellsBoundary (n : ℕ) :
    TopCat.HomotopyExtensionProperty (SSet.toTop.map (diagonalMap (replacementCellsBoundaryι H n)))
      :=
  homotopyExtensionProperty_realizedBisimplicialSigma
    (fun s : (nerve D).nonDegenerate n ↦ replacementCellBoundaryι H s)
    (fun s ↦ homotopyExtensionProperty_replacementCellBoundary H s)

/-- Each successor inclusion in the actual realized base-skeleton filtration
has the homotopy extension property. The attachment and boundary HEP are
proved from the real simplicial cells and their topological realizations. -/
theorem homotopyExtensionProperty_realizedReplacementSkeleton_succ (n : ℕ) :
    TopCat.HomotopyExtensionProperty ((realizedReplacementSkeleton H).map (homOfLE (Nat.le_succ
      n))) :=
  TopCat.homotopyExtensionProperty_pushout (realizedReplacementSkeleton_isPushout H n).flip
    (homotopyExtensionProperty_replacementCellsBoundary H n)

/-- Every inclusion between finite stages of the actual realized skeletal
tower has HEP. -/
theorem homotopyExtensionProperty_realizedReplacementSkeleton {n m : ℕ} (h : n ≤ m) :
    TopCat.HomotopyExtensionProperty ((realizedReplacementSkeleton H).map (homOfLE h)) := by
  induction m, h using Nat.le_induction with
  | base =>
    simpa using TopCat.homotopyExtensionProperty_of_isIso (𝟙 ((realizedReplacementSkeleton H).obj
      n))
  | succ m h ih =>
    have heq : (homOfLE (Nat.le_succ_of_le h)) = homOfLE h ≫ homOfLE (Nat.le_succ m) := rfl
    rw [heq, Functor.map_comp]
    exact TopCat.homotopyExtensionProperty_comp ih
      (homotopyExtensionProperty_realizedReplacementSkeleton_succ H m)

end CategoryTheory.TheoremA
