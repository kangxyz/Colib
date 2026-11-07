/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.ProductComparison
public import Colib.Topology.HELP.CompactLifting

/-! # Genuine compact HELP for the canonical realization-product map

The exact finite-right-support construction works in every source universe.
It gives compact HELP, with the entire prescribed boundary homotopy preserved,
for the original comparison. No unrestricted product homeomorphism is claimed.


Implementation provenance:
`Quillen/Topology/Realization/ProductCompactHELP.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u v

namespace SSet.ProductRealization
variable (X Y : SSet.{u})

/-- Exact compact-source lifting in arbitrary source universes. -/
theorem comparison_compact_lifts_universe
    (T : Type v) [TopologicalSpace T] [CompactSpace T] (f : C(T, |X| × |Y|)) :
    ∃ g : C(T, |X ⊗ Y|), (comparison X Y).comp g = f := by
  obtain ⟨B, hB, g, hg⟩ :=
    SSet.realization_continuousMap_factors_finiteSubcomplex (ContinuousMap.snd.comp f)
  let : SSet.Finite (B : SSet.{u}) := hB
  let k : C(T, |X| × |(B : SSet.{u})|) := (ContinuousMap.fst.comp f).prodMk g
  let l : C(T, |X ⊗ (B : SSet.{u})|) :=
    ((finiteRightHomeomorph X (B : SSet.{u})).symm : C(_, _)).comp k
  refine ⟨(SSet.toTop.map (X ◁ B.ι)).hom.comp l, ?_⟩
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, comparison_inclusion]
  have he : comparison X (B : SSet.{u}) (l t) = k t :=
    (finiteRightHomeomorph X (B : SSet.{u})).apply_symm_apply (k t)
  rw [he]
  exact _root_.Prod.ext rfl (DFunLike.congr_fun hg t)

/-- The original canonical comparison satisfies compact HELP for every
actual compact cofibration, retaining the whole boundary homotopy. -/
theorem comparison_compactHELP : CompactHomotopyExtensionLiftingProperty (comparison X Y) :=
  compactHELP_of_injective_compact_lifts (comparison X Y) (comparison_injective X Y)
    (comparison_compact_lifts_universe X Y)

end SSet.ProductRealization
