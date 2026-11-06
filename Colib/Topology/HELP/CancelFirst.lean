/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.StrictCompact
public import Colib.Topology.Homotopy.ExtensionContinuous
public import Colib.Topology.HELP.RetraceBoundary

/-! # Cancellation of the first compact HELP map

Lift the boundary through the first map, apply HELP for the composite, and
extend the boundary adjustment by HEP. The remaining backtracking homotopy
is contracted relative to both endpoints before invoking full HELP.


Implementation provenance:
`Quillen/Topology/HELP/CancelFirst.lean`
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

/-- Compact HELP lifts any map from a compact space up to an actual
homotopy, by applying the property to the empty cofibration. -/
theorem CompactHomotopyExtensionLiftingProperty.lift_compact
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}
    (hf : CompactHomotopyExtensionLiftingProperty f)
    (A : TopCat.{u}) [CompactSpace A] (a : C(A, Y)) :
    ∃ c : C(A, X), Nonempty ((f.comp c).Homotopy a) := by
  let E := TopCat.of PEmpty.{u+1}
  let i : E ⟶ A := TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩
  have hi : TopCat.HomotopyExtensionProperty i := by
    apply TopCat.homotopyExtensionProperty_of_continuous
    intro Z b H _
    exact ⟨b.comp ContinuousMap.snd, fun _ ↦ rfl, fun _ x ↦ isEmptyElim x⟩
  let a₀ : C(E, X) := ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let H : (f.comp a₀).Homotopy (a.comp i.hom) := {
    toFun z := isEmptyElim z.2
    continuous_toFun := continuous_of_discreteTopology
    map_zero_left x := isEmptyElim x
    map_one_left x := isEmptyElim x }
  obtain ⟨c, _, K, _⟩ := hf E A i hi a₀ a H
  exact ⟨c, ⟨K⟩⟩

/-- Cancel the first map: if `f` and the actual composite `g.comp f`
satisfy compact HELP, so does the original map `g`. -/
theorem CompactHomotopyExtensionLiftingProperty.cancel_first
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)} {g : C(Y, Z)}
    (hgf : CompactHomotopyExtensionLiftingProperty (g.comp f))
    (hf : CompactHomotopyExtensionLiftingProperty f) :
    CompactHomotopyExtensionLiftingProperty g := by
  apply CompactStrictHELP.full
  intro A B _ _ i hi a b w
  obtain ⟨a₀, ⟨L⟩⟩ := hf.lift_compact A a
  let T := (ContinuousMap.Homotopy.refl g).comp L
  obtain ⟨c₀, hc₀, K, hK⟩ := hgf A B i hi a₀ b (T.cast rfl w)
  obtain ⟨Q, hQ₀, hQA⟩ := TopCat.homotopyExtensionProperty_continuous hi
    (TopCat.of Y) (f.comp c₀) L.toContinuousMap (fun x ↦
      (L.map_zero_left x).trans (congrArg f (ContinuousMap.congr_fun hc₀ x)).symm)
  let c : C(B, Y) := ⟨fun x ↦ Q (1, x), by fun_prop⟩
  have hc : c.comp i.hom = a := by
    ext x
    exact (hQA 1 x).trans (L.map_one_left x)
  let R : (f.comp c₀).Homotopy c := {
    toContinuousMap := Q
    map_zero_left := hQ₀
    map_one_left _ := rfl }
  let J : (g.comp c).Homotopy b :=
    ((ContinuousMap.Homotopy.refl g).comp R).symm.trans K
  have hJ : (J.compContinuousMap i.hom).toContinuousMap =
      (T.symm.trans T).toContinuousMap := by
    ext ⟨t, x⟩
    change J (t, i x) = (T.symm.trans T) (t, x)
    simp only [J, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · change g (Q (unitInterval.symm _, i x)) = g (L (unitInterval.symm _, x))
      rw [hQA]
      rfl
    · exact hK _ x
  let J₀ : ((g.comp c).comp i.hom).Homotopy (b.comp i.hom) :=
    (ContinuousMap.Homotopy.refl (g.comp a)).cast
      (by rw [ContinuousMap.comp_assoc, hc]) w
  have hrel : (J.compContinuousMap i.hom).toContinuousMap.HomotopyRel
      J₀.toContinuousMap {z : unitInterval × A | z.1 = 0 ∨ z.1 = 1} :=
    (retraceHomotopy T).cast hJ.symm rfl
  obtain ⟨J', hJ'⟩ := TopCat.homotopyExtensionProperty_correct_boundary hi
    (Z := TopCat.of Z) J J₀ hrel
  refine ⟨c, hc, ⟨{ J' with prop' := ?_ }⟩⟩
  rintro t _ ⟨x, rfl⟩
  exact (hJ' t x).trans (congrArg g (ContinuousMap.congr_fun hc x)).symm

end Topology
