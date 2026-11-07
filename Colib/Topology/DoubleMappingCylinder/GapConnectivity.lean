/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.GapCollarComparison
public import Colib.Topology.DoubleMappingCylinder.CollarGapConnectivity
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.HomotopySquare

/-!
# Finite homotopy excision for the actual original double-cylinder gap

If the original attaching maps f and g are p- and q-connected, the canonical original gap
`a ↦ (g(a), f(a), t ↦ l(a,t))` is r-connected whenever r+1≤p+q. The proof transfers genuine
open-cover excision through the actual band section, endpoint collar equivalences, and explicit
original cylinder-time homotopy. Fixed cuts and their midpoint remove all auxiliary choices
from the theorem's hypotheses. No separation, CW type or attaching-map cofibration is assumed.
The conclusion includes every target component and every actual fiber basepoint. Reduced
base-line collapse and stable cofiber excision remain distinct point-set and stabilization steps.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/GapConnectivity.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat.DoubleCylinder

/-- The original full-cylinder gap satisfies the finite excision range. The exact original
pushout, attaching maps and full stored paths remain in the conclusion. -/
theorem gap_isHomotopyConnectedMap {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (p q r : ℕ) (hr : r + 1 ≤ p + q)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q) :
    IsHomotopyConnectedMap (gap f g sq) r := by
  let lo : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩
  let hi : unitInterval := ⟨2 / 3, by constructor <;> norm_num⟩
  have hcut : lo < hi := by change (1 / 3 : ℝ) < 2 / 3; norm_num
  have hhi : 0 < hi := lt_of_le_of_lt bot_le hcut
  have hlo : lo < 1 := lt_of_lt_of_le hcut le_top
  let c := bandMidpoint lo hi hcut
  let source := gapOverlapEquiv f g sq lo hi c
  let target := gapTargetCollarEquiv f g sq lo hi hhi hlo
  exact IsHomotopyConnectedMap.of_weak_homotopy_square source.toFun target.toFun
    (gapCollarHomotopy f g sq lo hi c hhi hlo)
    (isWeakHomotopyEquivalence_of_homotopyEquiv source)
    (isWeakHomotopyEquivalence_of_homotopyEquiv target) r
    (collarGap_isHomotopyConnectedMap f g sq lo hi hcut p q r hr hf hg)

end TopCat.DoubleCylinder

attribute [colib_tag "COL-0287",
  colib_ref "HatcherAT" "Section 4.2, Theorem 4.23, p. 360; proof, pp. 361-363" "background"
    "Classical CW-pair excision; the all-fiber double-cylinder extension is proved here"]
  TopCat.DoubleCylinder.gap_isHomotopyConnectedMap
