/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.CancelSecond
public import Colib.Topology.HomotopyLifting.Compact.OverBaseCorrection

/-! # Full relative homotopy lifting through an actual compact HELP map

The ordinary HELP map lifts the genuine side-and-caps cylinder boundary.
Compact-parameter base correction keeps that entire boundary literally fixed.
No strict-fiber equivalence or inverse family is an input.


Implementation provenance:
`Quillen/Topology/HELP/CompactVerticalCancellation.lean`
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

/-- The product duration vanishes on exactly the whole original cylinder
boundary, including both caps and every side point. -/
theorem cylinderBoundary_duration_zero_iff {A D : TopCat.{u}} (i : A ⟶ D)
    (d : C(D, unitInterval)) (hd : ∀ x, d x = 0 ↔ x ∈ Set.range i)
    (z : D × unitInterval) :
    (d z.1 * z.2) * unitInterval.symm z.2 = 0 ↔ z ∈ Set.range
      (TopCat.CylinderBoundary.cylinderBoundaryMap i) := by
  have hside (a : A) (t : unitInterval) :
      TopCat.CylinderBoundary.cylinderBoundaryMap i (TopCat.CylinderBoundary.cylinderBoundarySide
        i (a,t)) = (i a,t) :=
    ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundarySide_map i) (a,t)
  have hcap₀ (x : D) : TopCat.CylinderBoundary.cylinderBoundaryMap i
    (TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inl x)) = (x,0) :=
    ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i) (.inl x)
  have hcap₁ (x : D) : TopCat.CylinderBoundary.cylinderBoundaryMap i
    (TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inr x)) = (x,1) :=
    ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i) (.inr x)
  constructor
  · intro hz
    have hz' : d z.1 = 0 ∨ z.2 = 0 ∨ z.2 = 1 := by
      simpa only [mul_eq_zero,unitInterval.symm_eq_zero,or_assoc] using hz
    rcases z with ⟨x,t⟩
    rcases hz' with hx | ht | ht
    · obtain ⟨a,rfl⟩ := (hd x).mp hx
      exact ⟨TopCat.CylinderBoundary.cylinderBoundarySide i (a,t),hside a t⟩
    · change t = 0 at ht
      subst t
      exact ⟨TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inl x),hcap₀ x⟩
    · change t = 1 at ht
      subst t
      exact ⟨TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inr x),hcap₁ x⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨z,rfl⟩ := pushout_sum_surjective (TopCat.CylinderBoundary.cylinderBoundary_isPushout i)
      z
    rcases z with ⟨a,t⟩ | (x | x)
    · change (d ((TopCat.CylinderBoundary.cylinderBoundaryMap i
        (TopCat.CylinderBoundary.cylinderBoundarySide i (a,t))).1) *
        (TopCat.CylinderBoundary.cylinderBoundaryMap i
          (TopCat.CylinderBoundary.cylinderBoundarySide i (a,t))).2) *
        unitInterval.symm (TopCat.CylinderBoundary.cylinderBoundaryMap i
          (TopCat.CylinderBoundary.cylinderBoundarySide i (a,t))).2 = 0
      rw [hside,(hd (i a)).mpr ⟨a,rfl⟩,zero_mul,zero_mul]
    · change (d ((TopCat.CylinderBoundary.cylinderBoundaryMap i
        (TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inl x))).1) *
        (TopCat.CylinderBoundary.cylinderBoundaryMap i
          (TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inl x))).2) *
        unitInterval.symm (TopCat.CylinderBoundary.cylinderBoundaryMap i
          (TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inl x))).2 = 0
      rw [hcap₀,mul_zero,zero_mul]
    · change (d ((TopCat.CylinderBoundary.cylinderBoundaryMap i
        (TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inr x))).1) *
        (TopCat.CylinderBoundary.cylinderBoundaryMap i
          (TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inr x))).2) *
        unitInterval.symm (TopCat.CylinderBoundary.cylinderBoundaryMap i
          (TopCat.CylinderBoundary.cylinderBoundaryCaps i (.inr x))).2 = 0
      rw [hcap₁,unitInterval.symm_one,mul_zero]

/-- Lift the original full relative homotopy through `g`, keeping its base
coordinate and the exact prescribed side and both endpoint maps. -/
theorem compact_vertical_homotopy_lift
    {Y Z B : Type u} [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace B]
    (p : C(Y, B)) (q : C(Z, B)) (g : C(Y, Z)) (sq : q.comp g = p)
    (hp : CompactHomotopyLiftingProperty p) (hq : CompactHomotopyLiftingProperty q)
    (hg : CompactHomotopyExtensionLiftingProperty g)
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D] [LocallyCompactSpace D]
    (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (duration : C(D, unitInterval)) (hzero : ∀ x, duration x = 0 ↔ x ∈ Set.range i)
    (U V : C(D, Y)) (H : (U.comp i.hom).Homotopy (V.comp i.hom))
    (K : (g.comp U).Homotopy (g.comp V))
    (hK : HomotopyOver (p.comp V) q K) (hside : ∀ t a, K (t, i a) = g (H (t, a))) :
    ∃ L : U.Homotopy V,HomotopyOver (p.comp V) p L ∧ ∀ t a,L (t,i a) = H (t,a) := by
  let S : TopCat.of (A × unitInterval) ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨fun z ↦ H (z.2,z.1),by fun_prop⟩
  let E : TopCat.of (D ⊕ D) ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨Sum.elim U V,U.continuous.sumElim V.continuous⟩
  have w : TopCat.CylinderBoundary.cylinderBoundaryEnds A ≫ S =
    TopCat.CylinderBoundary.cylinderBoundarySumMap i ≫ E := by
    ext x
    rcases x with a | a
    · exact H.map_zero_left a
    · exact H.map_one_left a
  let a : TopCat.CylinderBoundary i ⟶ TopCat.of Y := pushout.desc S E w
  have hS : TopCat.CylinderBoundary.cylinderBoundarySide i ≫ a = S := pushout.inl_desc _ _ _
  have hE : TopCat.CylinderBoundary.cylinderBoundaryCaps i ≫ a = E := pushout.inr_desc _ _ _
  let k : C(D × unitInterval,Z) := ⟨fun z ↦ K (z.2,z.1),by fun_prop⟩
  have hw' : a ≫ TopCat.ofHom g = TopCat.CylinderBoundary.cylinderBoundaryMap i ≫ TopCat.ofHom k :=
    by
    apply (TopCat.CylinderBoundary.cylinderBoundary_isPushout i).hom_ext
    · rw [← Category.assoc,hS,← Category.assoc,TopCat.CylinderBoundary.cylinderBoundarySide_map]
      ext ⟨a,t⟩
      exact (hside t a).symm
    · rw [← Category.assoc,hE,← Category.assoc,TopCat.CylinderBoundary.cylinderBoundaryCaps_map]
      ext x
      rcases x with x | x
      · exact (K.map_zero_left x).symm
      · exact (K.map_one_left x).symm
  have hw : g.comp a.hom = k.comp (TopCat.CylinderBoundary.cylinderBoundaryMap i).hom :=
    congrArg TopCat.Hom.hom hw'
  obtain ⟨l,hl,⟨J⟩⟩ := hg.strict (TopCat.CylinderBoundary i) (TopCat.of (D × unitInterval))
    (TopCat.CylinderBoundary.cylinderBoundaryMap i)
      (TopCat.CylinderBoundary.homotopyExtensionProperty_cylinderBoundaryMap i hi) a.hom k hw
  let d : C(D × unitInterval,unitInterval) :=
    ⟨fun z ↦ (duration z.1 * z.2) * unitInterval.symm z.2,by fun_prop⟩
  obtain ⟨l',hbase,hfix,_,_,_⟩ := compact_correct_comparison_over_fixed_zero p q g sq hp hq l k
    J.toHomotopy d (by
    intro z hz t
    exact J.prop t z ((cylinderBoundary_duration_zero_iff i duration hzero z).mp hz))
  have hb : ∀ x,l' (TopCat.CylinderBoundary.cylinderBoundaryMap i x) = a x := by
    intro x
    exact (hfix _ ((cylinderBoundary_duration_zero_iff i duration hzero _).mpr ⟨x,rfl⟩)).trans
      (ContinuousMap.congr_fun hl x)
  have hLside (a₀ : A) (t : unitInterval) : l' (i a₀,t) = H (t,a₀) :=
    (congrArg l' (ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundarySide_map i)
      (a₀,t))).symm.trans
      ((hb _).trans (ConcreteCategory.congr_hom hS (a₀,t)))
  let L : U.Homotopy V := {
    toFun z := l' (z.2,z.1)
    continuous_toFun := by fun_prop
    map_zero_left x :=
      (congrArg l' (ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i)
        (.inl x))).symm.trans
        ((hb _).trans (ConcreteCategory.congr_hom hE (.inl x)))
    map_one_left x :=
      (congrArg l' (ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i)
        (.inr x))).symm.trans
        ((hb _).trans (ConcreteCategory.congr_hom hE (.inr x))) }
  refine ⟨L,?_,fun t a ↦ hLside a t⟩
  intro t x
  exact (ContinuousMap.congr_fun hbase (x,t)).trans (hK t x)

end Topology
