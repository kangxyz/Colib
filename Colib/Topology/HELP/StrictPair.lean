/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.StrictCompact

/-! # Full prescribed-boundary HELP for one actual HEP pair

The strict-to-full construction keeps its test spaces and inclusion fixed.
This version exposes that fact so it applies to genuinely contracted tests
without claiming a lifting property on arbitrary compact target spaces.


Implementation provenance:
`Quillen/Topology/HELP/StrictPair.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology

/-- Strict-square lifting for this particular HEP pair recovers the full
prescribed homotopy on exactly this pair. -/
theorem fullHELP_at_pair_of_strict {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A B : TopCat.{u}) (i : A ⟶ B)
    (hi : TopCat.HomotopyExtensionProperty i)
    (hf : ∀ (a : C(A, X)) (b : C(B, Y)), f.comp a = b.comp i.hom →
      ∃ c : C(B, X), c.comp i.hom = a ∧ Nonempty ((f.comp c).HomotopyRel b (Set.range i)))
    (a : C(A, X)) (b : C(B, Y)) (H : (f.comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(B,X), c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
      ∀ t x, K (t, i x) = H (t,x) := by
  obtain ⟨Q, hQ₀, hQA⟩ := TopCat.homotopyExtensionProperty_continuous hi
    (TopCat.of Y) b H.symm.toContinuousMap (fun x ↦ H.symm.map_zero_left x)
  let b' : C(B, Y) := ⟨fun x ↦ Q (1, x), by fun_prop⟩
  let T : b.Homotopy b' := {
    toContinuousMap := Q
    map_zero_left := hQ₀
    map_one_left := fun _ ↦ rfl }
  have hw : f.comp a = b'.comp i.hom := by
    ext x
    exact ((hQA 1 x).trans (H.symm.map_one_left x)).symm
  obtain ⟨c, hc, ⟨K⟩⟩ := hf a b' hw
  let L := K.toHomotopy.trans T.symm
  let H' : ((f.comp c).comp i.hom).Homotopy (b.comp i.hom) :=
    H.cast (by rw [ContinuousMap.comp_assoc, hc]) rfl
  have hL : ∀ t x, L (t, i x) = Path.delayReflLeft 0 (H'.evalAt x) t := by
    intro t x
    rw [Path.delayReflLeft_zero]
    simp only [L, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    · exact K.prop _ (i x) ⟨x, rfl⟩
    · change Q (unitInterval.symm _, i x) = H (_, x)
      rw [hQA]
      simp
  obtain ⟨L', hL'⟩ := TopCat.homotopyExtensionProperty_unpad_boundary hi
    (Z := TopCat.of Y) L H' hL
  exact ⟨c, hc, L', hL'⟩

end Topology
