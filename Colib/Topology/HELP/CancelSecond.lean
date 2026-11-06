/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.StrictCompact
public import Colib.Topology.HELP.CylinderBoundary

/-! # Cancellation of the second compact HELP map

The second HELP map is applied to the genuine compact pushout boundary of a
cylinder. The resulting map has exactly the required endpoints and the full
original side homotopy; its further comparison homotopy is not needed.


Implementation provenance:
`Quillen/Topology/HELP/CancelSecond.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
namespace Topology

/-- Cancel the second map: compact HELP for `g` and the actual composite
`g.comp f` implies full compact HELP for the original map `f`. -/
theorem CompactHomotopyExtensionLiftingProperty.cancel_second
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)} {g : C(Y, Z)}
    (hgf : CompactHomotopyExtensionLiftingProperty (g.comp f))
    (hg : CompactHomotopyExtensionLiftingProperty g) :
    CompactHomotopyExtensionLiftingProperty f := by
  intro A B _ _ i hi a b H
  obtain ⟨c, hc, K, hK⟩ := hgf A B i hi a (g.comp b)
    ((ContinuousMap.Homotopy.refl g).comp H)
  let S : TopCat.of (A × unitInterval) ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨fun z ↦ H (z.2, z.1), by fun_prop⟩
  let E : TopCat.of (B ⊕ B) ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨Sum.elim (f.comp c) b, (f.comp c).continuous.sumElim b.continuous⟩
  have w : TopCat.CylinderBoundary.cylinderBoundaryEnds A ≫ S =
    TopCat.CylinderBoundary.cylinderBoundarySumMap i ≫ E := by
    ext x
    rcases x with a | a
    · exact (H.map_zero_left a).trans (congrArg f (ContinuousMap.congr_fun hc a)).symm
    · exact H.map_one_left a
  let d : TopCat.CylinderBoundary i ⟶ TopCat.of Y := pushout.desc S E w
  have hS : TopCat.CylinderBoundary.cylinderBoundarySide i ≫ d = S := pushout.inl_desc _ _ _
  have hE : TopCat.CylinderBoundary.cylinderBoundaryCaps i ≫ d = E := pushout.inr_desc _ _ _
  let k : TopCat.of (B × unitInterval) ⟶ TopCat.of Z :=
    TopCat.ofHom ⟨fun z ↦ K (z.2, z.1), by fun_prop⟩
  have hw : d ≫ TopCat.ofHom g = TopCat.CylinderBoundary.cylinderBoundaryMap i ≫ k := by
    apply (TopCat.CylinderBoundary.cylinderBoundary_isPushout i).hom_ext
    · rw [← Category.assoc, hS, ← Category.assoc, TopCat.CylinderBoundary.cylinderBoundarySide_map]
      ext ⟨a, t⟩
      exact (hK t a).symm
    · rw [← Category.assoc, hE, ← Category.assoc, TopCat.CylinderBoundary.cylinderBoundaryCaps_map]
      ext x
      rcases x with b | b
      · exact (K.map_zero_left b).symm
      · exact (K.map_one_left b).symm
  have hw' : g.comp d.hom = k.hom.comp (TopCat.CylinderBoundary.cylinderBoundaryMap i).hom :=
    congrArg TopCat.Hom.hom hw
  obtain ⟨l, hl, _⟩ := hg.strict (TopCat.CylinderBoundary i) (TopCat.of (B × unitInterval))
    (TopCat.CylinderBoundary.cylinderBoundaryMap i)
      (TopCat.CylinderBoundary.homotopyExtensionProperty_cylinderBoundaryMap i hi) d.hom k.hom hw'
  have hside (a : A) (t : unitInterval) : l (i a, t) = H (t, a) := by
    have h := ContinuousMap.congr_fun hl (TopCat.CylinderBoundary.cylinderBoundarySide i (a, t))
    have hs := ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundarySide_map i) (a,
      t)
    have hd := ConcreteCategory.congr_hom hS (a, t)
    exact (congrArg l hs).symm.trans (h.trans hd)
  have hzero (b : B) : l (b, 0) = f (c b) := by
    have h := ContinuousMap.congr_fun hl (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl
      b))
    have hs := ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i)
      (Sum.inl b)
    have hd := ConcreteCategory.congr_hom hE (Sum.inl b)
    exact (congrArg l hs).symm.trans (h.trans hd)
  refine ⟨c, hc, {
    toFun z := l (z.2, z.1)
    continuous_toFun := by fun_prop
    map_zero_left := hzero
    map_one_left := ?_ }, fun t x ↦ hside x t⟩
  intro x
  have h := ContinuousMap.congr_fun hl (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr x))
  have hs := ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i)
    (Sum.inr x)
  have hd := ConcreteCategory.congr_hom hE (Sum.inr x)
  exact (congrArg l hs).symm.trans (h.trans hd)

end Topology
