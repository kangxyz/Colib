/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-!
# Naturality of the fundamental-group identification

Adapted from `Quillen/KTheory/GrothendieckComparison/Naturality.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, specified basepoint equalities and multiplication order are retained.
-/

@[expose] public noncomputable section

open scoped Topology

/-- The actual π₁/fundamental-group isomorphism respects based continuous maps. -/
lemma HomotopyGroup.pi1MulEquivFundamentalGroup_naturality
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (HomotopyGroup.map f h a) =
      FundamentalGroup.mapOfEq f h (HomotopyGroup.pi1MulEquivFundamentalGroup a) := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [FundamentalGroup.mapOfEq_apply]
    change (⟦genLoopEquivOfUnique (Fin 1) (GenLoop.postcomp f h p)⟧ :
      FundamentalGroup Y y) =
      ⟦((genLoopEquivOfUnique (Fin 1) p).map f.continuous).cast h.symm h.symm⟧
    congr 1
