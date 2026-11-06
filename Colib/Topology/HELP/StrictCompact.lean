/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.Compact
public import Colib.Topology.Homotopy.BoundaryCorrection

/-! # Strict-square characterization of compact HELP

The relative homotopy in a strict square is fixed on the entire image of the
cofibration. Conversely, reversing and extending the prescribed boundary
homotopy reduces full HELP to a strict square. The temporary constant prefix
is removed by the actual relative interval-square extension theorem.


Implementation provenance:
`Quillen/Topology/HELP/StrictCompact.lean`
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

/-- Compact strict-square HELP, with an actual homotopy relative to the
whole image of the given cofibration. -/
def CompactStrictHELP {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  ∀ (A B : TopCat.{u}) [CompactSpace A] [CompactSpace B] (i : A ⟶ B),
    TopCat.HomotopyExtensionProperty i →
    ∀ (a : C(A, X)) (b : C(B, Y)), f.comp a = b.comp i.hom →
      ∃ c : C(B, X), c.comp i.hom = a ∧
        Nonempty ((f.comp c).HomotopyRel b (Set.range i))

theorem CompactHomotopyExtensionLiftingProperty.strict
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}
    (hf : CompactHomotopyExtensionLiftingProperty f) : CompactStrictHELP f := by
  intro A B _ _ i hi a b w
  let H := (ContinuousMap.Homotopy.refl (f.comp a)).cast rfl w
  obtain ⟨c, hc, K, hK⟩ := hf A B i hi a b H
  refine ⟨c, hc, ⟨{ K with prop' := ?_ }⟩⟩
  rintro t _ ⟨x, rfl⟩
  exact (hK t x).trans (congrArg f (ContinuousMap.congr_fun hc x)).symm

theorem CompactStrictHELP.full
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}
    (hf : CompactStrictHELP f) : CompactHomotopyExtensionLiftingProperty f := by
  intro A B _ _ i hi a b H
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
  obtain ⟨c, hc, ⟨K⟩⟩ := hf A B i hi a b' hw
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

theorem compactHELP_iff_strict {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    CompactHomotopyExtensionLiftingProperty f ↔ CompactStrictHELP f :=
  ⟨fun h ↦ h.strict, fun h ↦ h.full⟩

end Topology
