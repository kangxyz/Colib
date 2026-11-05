/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module
public import Colib.Topology.Realization.ProductComparison
@[expose] public noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Topology
open scoped Simplicial Topology
universe u
example (X Y : SSet.{u}) :
    Function.Injective (SSet.ProductRealization.comparison X Y) :=
  SSet.ProductRealization.comparison_injective X Y
example (X Y : SSet.{u}) :
    HasCompactSourceLifts (SSet.ProductRealization.comparison X Y) :=
  SSet.ProductRealization.comparison_compact_lifts X Y
example (X Y : SSet.{u}) (p : |X ⊗ Y|) :
    (SSet.ProductRealization.comparisonPiEquiv X Y p 0 :
      HomotopyGroup.Pi 1 |X ⊗ Y| p →*
        HomotopyGroup.Pi 1 (|X| × |Y|) (SSet.ProductRealization.comparison X Y p)) =
      HomotopyGroup.piMap 0 (SSet.ProductRealization.comparison X Y) rfl := rfl
example (X Y : SSet.{u}) [Y.Finite] :
    (SSet.ProductRealization.finiteRightHomeomorph X Y : C(_, _)) =
      SSet.ProductRealization.comparison X Y := rfl
example (X Y : SSet.{u}) (p : |X ⊗ Y|) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) |X ⊗ Y| p ≃*
      HomotopyGroup.Pi (n + 1) |X| (SSet.ProductRealization.comparison X Y p).1 ×
        HomotopyGroup.Pi (n + 1) |Y| (SSet.ProductRealization.comparison X Y p).2 :=
  SSet.ProductRealization.piEquiv X Y p n
