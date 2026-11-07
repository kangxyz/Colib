/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.StrictCompact
public import Colib.Topology.HELP.RetraceBoundary

/-! # Homotopy invariance of genuine compact HELP

Changing the forward map introduces a reversed boundary path followed by
itself. The explicit relative retracing contraction removes this exactly.


Implementation provenance:
`Quillen/Topology/HELP/HomotopyInvariance.lean`
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

/-- Compact HELP is invariant under an actual homotopy of the original
continuous maps, with the full prescribed boundary convention unchanged. -/
theorem CompactHomotopyExtensionLiftingProperty.of_homotopy
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (hf : CompactHomotopyExtensionLiftingProperty f) (H : f.Homotopy g) :
    CompactHomotopyExtensionLiftingProperty g := by
  apply CompactStrictHELP.full
  intro A B _ _ i hi a b w
  let T := H.compContinuousMap a
  obtain ⟨c, hc, K, hK⟩ := hf A B i hi a b (T.cast rfl w)
  let J := (H.compContinuousMap c).symm.trans K
  have hJ : (J.compContinuousMap i.hom).toContinuousMap =
      (T.symm.trans T).toContinuousMap := by
    ext ⟨t, x⟩
    change J (t, i x) = (T.symm.trans T) (t, x)
    simp only [J, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · change H (unitInterval.symm _, c (i x)) = H (unitInterval.symm _, a x)
      apply congrArg H
      apply Prod.ext
      · rfl
      · exact ContinuousMap.congr_fun hc x
    · exact hK _ x
  let J₀ : ((g.comp c).comp i.hom).Homotopy (b.comp i.hom) :=
    (ContinuousMap.Homotopy.refl (g.comp a)).cast
      (by rw [ContinuousMap.comp_assoc, hc]) w
  have hrel : (J.compContinuousMap i.hom).toContinuousMap.HomotopyRel
      J₀.toContinuousMap {z : unitInterval × A | z.1 = 0 ∨ z.1 = 1} :=
    (retraceHomotopy T).cast hJ.symm rfl
  obtain ⟨J', hJ'⟩ := TopCat.homotopyExtensionProperty_correct_boundary hi
    (Z := TopCat.of Y) J J₀ hrel
  refine ⟨c, hc, ⟨{ J' with prop' := ?_ }⟩⟩
  rintro t _ ⟨x, rfl⟩
  exact (hJ' t x).trans (congrArg g (ContinuousMap.congr_fun hc x)).symm

/-- Propositional homotopy invariance, requiring no chosen inverse maps. -/
theorem compactHELP_iff_of_homotopic {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)} (H : f.Homotopic g) :
    CompactHomotopyExtensionLiftingProperty f ↔ CompactHomotopyExtensionLiftingProperty g := by
  obtain ⟨H⟩ := H
  exact ⟨fun hf ↦ hf.of_homotopy H, fun hg ↦ hg.of_homotopy H.symm⟩

end Topology
