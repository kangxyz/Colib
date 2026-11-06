/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.StrictHomotopyEquiv
public import Colib.Topology.Homotopy.BoundaryCorrection
public import Colib.Topology.HELP.Compact

/-! Actual homotopy equivalences satisfy HELP with the whole prescribed
boundary homotopy retained exactly. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/HomotopyEquiv.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, homotopies,
hypotheses and universes are retained; imports use native lower owners. -/
@[expose] public section

noncomputable section
universe u
open TopCat Topology CategoryTheory
open scoped Topology unitInterval
open unitInterval
namespace TopCat

/-- Homotopy extension and lifting for a genuine homotopy equivalence.
No based/relative inverse data are assumed. -/
theorem homotopyEquiv_HELP {A B X Y : TopCat.{u}} {i : A ⟶ B}
    (hi : TopCat.HomotopyExtensionProperty i) (e : ContinuousMap.HomotopyEquiv X Y)
    (a : C(A, X)) (b : C(B, Y)) (H : (e.toFun.comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(B,X), c.comp i.hom = a ∧ ∃ K : (e.toFun.comp c).Homotopy b,
      ∀ t x, K (t,i x) = H (t,x) := by
  obtain ⟨Q,hQ₀,hQA⟩ := TopCat.homotopyExtensionProperty_continuous hi Y b
    H.symm.toContinuousMap (fun x ↦ H.symm.map_zero_left x)
  let b' : C(B,Y) := ⟨fun x ↦ Q (1,x), by fun_prop⟩
  let T : b.Homotopy b' := {
    toContinuousMap := Q
    map_zero_left := hQ₀
    map_one_left := fun _ ↦ rfl }
  have hw : e.toFun.comp a = b'.comp i.hom := by
    ext x
    exact ((hQA 1 x).trans (H.symm.map_one_left x)).symm
  obtain ⟨c,hc,⟨K⟩⟩ := TopCat.homotopyEquiv_strictHELP hi e a b' hw
  let L := K.toHomotopy.trans T.symm
  let H' : ((e.toFun.comp c).comp i.hom).Homotopy (b.comp i.hom) :=
    H.cast (by rw [ContinuousMap.comp_assoc,hc]) rfl
  have hL : ∀ t x, L (t,i x) = Path.delayReflLeft 0 (H'.evalAt x) t := by
    intro t x
    rw [Path.delayReflLeft_zero]
    simp only [L, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs with ht
    · exact K.prop _ (i x) ⟨x,rfl⟩
    · change Q (unitInterval.symm _, i x) = H (_, x)
      rw [hQA]
      simp
  obtain ⟨L',hL'⟩ := TopCat.homotopyExtensionProperty_unpad_boundary hi L H' hL
  exact ⟨c,hc,L',hL'⟩

end TopCat
namespace TopCat

/-- The compact HELP property follows from an actual homotopy equivalence. -/
theorem compactHELP_of_homotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : CompactHomotopyExtensionLiftingProperty e.toFun := by
  intro A B _ _ i hi a b H
  exact TopCat.homotopyEquiv_HELP (X := TopCat.of X) (Y := TopCat.of Y) hi e a b H

end TopCat
