/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.Compact

/-! # Compact HELP from exact compact lifting

An injective map with exact continuous lifts of compact-source maps satisfies
compact HELP. The complete prescribed boundary homotopy is retained: lift it,
then extend its reverse across the actual cofibration before reversing back.


Implementation provenance:
`Quillen/Topology/HELP/CompactLifting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u

namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Exact compact lifting and injectivity imply genuine compact HELP, with
no homotopy-equivalence or fiber-equivalence premise. -/
theorem compactHELP_of_injective_compact_lifts (e : C(X, Y))
    (he : Function.Injective e)
    (hl : ∀ (T : Type u) [TopologicalSpace T] [CompactSpace T] (f : C(T, Y)),
      ∃ g : C(T, X), e.comp g = f) :
    CompactHomotopyExtensionLiftingProperty e := by
  intro A B _ _ i hi a b H
  obtain ⟨c, hc⟩ := hl B b
  obtain ⟨L, hL⟩ := hl (unitInterval × A) H.toContinuousMap
  let K : a.Homotopy (c.comp i.hom) := {
    toContinuousMap := L
    map_zero_left x := he ((ContinuousMap.congr_fun hL (0, x)).trans (H.map_zero_left x))
    map_one_left x := he ((ContinuousMap.congr_fun hL (1, x)).trans
      ((H.map_one_left x).trans (ContinuousMap.congr_fun hc (i x)).symm)) }
  obtain ⟨Q, hQ₀, hQA⟩ := TopCat.homotopyExtensionProperty_continuous hi
    (TopCat.of X) c K.symm.toContinuousMap (fun x ↦ K.symm.map_zero_left x)
  let d : C(B, X) := ⟨fun x ↦ Q (1, x), by fun_prop⟩
  have hd : d.comp i.hom = a := by
    apply ContinuousMap.ext
    intro x
    exact (hQA 1 x).trans (K.symm.map_one_left x)
  let J : c.Homotopy d := {
    toContinuousMap := Q
    map_zero_left := hQ₀
    map_one_left _ := rfl }
  refine ⟨d, hd, ((ContinuousMap.Homotopy.refl e).comp J.symm).cast rfl hc, ?_⟩
  intro t x
  change e (Q (unitInterval.symm t, i x)) = H (t, x)
  rw [hQA]
  change e (L (unitInterval.symm (unitInterval.symm t), x)) = H (t, x)
  rw [unitInterval.symm_symm]
  exact ContinuousMap.congr_fun hL (t, x)

end Topology
