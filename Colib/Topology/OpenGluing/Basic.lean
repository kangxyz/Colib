/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Pushout.Open.Attachment
public import Colib.Topology.DeformationRetract.FiberwisePushout
public import Colib.Topology.HomotopyLifting.Closure
public import Colib.Topology.HomotopyLifting.Collar.TwoCharts

/-!
# Normalized two-open gluing

The total space is an iterated ordinary topological pushout of two genuine
fibrations and a fiberwise strong-deformation bridge over their overlap.
Its weak covering-homotopy lifting is proved from its actual open charts.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/OpenGluing/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section

open Topology

noncomputable section
open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.OpenGluing

/-- Primitive geometric data for normalized gluing. No lifting property of
the glued projection or of a restriction of the glued space is assumed. -/
structure Data (T : TopCat.{u}) (U V : Set T) where
  /-- The space over `U` forming the left end of the gluing. -/
  E0 : TopCat.{u}
  /-- The space over `V` forming the right end of the gluing. -/
  E1 : TopCat.{u}
  /-- The bridge space over the overlap `U ∩ V`. -/
  M : TopCat.{u}
  /-- The projection from the left end to the subspace `U`. -/
  p0 : E0 ⟶ TopCat.of U
  /-- The projection from the right end to the subspace `V`. -/
  p1 : E1 ⟶ TopCat.of V
  /-- The bridge projection to the subspace `U ∩ V`. -/
  q : M ⟶ TopCat.of (U ∩ V : Set T)
  /-- Attach the part of the left end lying over `V` to the bridge. -/
  i0 : TopCat.of {e : E0 // (p0 e).1 ∈ V} ⟶ M
  /-- Attach the part of the right end lying over `U` to the bridge. -/
  i1 : TopCat.of {e : E1 // (p1 e).1 ∈ U} ⟶ M
  /-- The left attachment preserves the underlying point of `T`. -/
  over0 : ∀ e, (q (i0 e)).1 = (p0 e.1).1
  /-- The right attachment preserves the underlying point of `T`. -/
  over1 : ∀ e, (q (i1 e)).1 = (p1 e.1).1

namespace Data
variable {T : TopCat.{u}} {U V : Set T} (d : Data T U V)

/-- The restriction of the left end to the overlap `U ∩ V`. -/
abbrev Q0 : TopCat.{u} := TopCat.of {e : d.E0 // (d.p0 e).1 ∈ V}
/-- The restriction of the right end to the overlap `U ∩ V`. -/
abbrev Q1 : TopCat.{u} := TopCat.of {e : d.E1 // (d.p1 e).1 ∈ U}
/-- The left projection regarded as a map to the ambient base `T`. -/
def base0 : d.E0 ⟶ T := TopCat.ofHom ⟨fun e ↦ (d.p0 e).1, by fun_prop⟩
/-- The right projection regarded as a map to the ambient base `T`. -/
def base1 : d.E1 ⟶ T := TopCat.ofHom ⟨fun e ↦ (d.p1 e).1, by fun_prop⟩
/-- The bridge projection regarded as a map to the ambient base `T`. -/
def bridgeBase : d.M ⟶ T := TopCat.ofHom ⟨fun m ↦ (d.q m).1, by fun_prop⟩
/-- The bridge projection to the left subspace `U`, forgetting membership in `V`. -/
def bridgeLeft : d.M ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun m ↦ ⟨(d.q m).1, (d.q m).2.1⟩, by fun_prop⟩
/-- The bridge projection to the right subspace `V`, forgetting membership in `U`. -/
def bridgeRight : d.M ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun m ↦ ⟨(d.q m).1, (d.q m).2.2⟩, by fun_prop⟩
/-- Include the overlap restriction `Q0` into the left end `E0`. -/
abbrev inclusion0 : d.Q0 ⟶ d.E0 := OpenAttachment.inclusion d.base0 V
/-- Include the overlap restriction `Q1` into the right end `E1`. -/
abbrev inclusion1 : d.Q1 ⟶ d.E1 := OpenAttachment.inclusion d.base1 U

/-- The pushout attaching the left end `E0` to the bridge `M` along `Q0`. -/
abbrev First : TopCat.{u} := pushout d.i0 d.inclusion0
/-- The bridge inclusion into the first pushout attachment. -/
abbrev firstBridge : d.M ⟶ d.First := pushout.inl _ _
/-- The left-end inclusion into the first pushout attachment. -/
abbrev firstEnd : d.E0 ⟶ d.First := pushout.inr _ _
theorem first_isPushout : IsPushout d.i0 d.inclusion0 d.firstBridge d.firstEnd :=
  IsPushout.of_hasPushout _ _

/-- The map from the first attachment to `U`, induced by `bridgeLeft` and `p0` using the
compatibility of the left attachment with the base. -/
def firstProjection : d.First ⟶ TopCat.of U := pushout.desc d.bridgeLeft d.p0 (by
  apply ConcreteCategory.hom_ext
  intro e
  exact Subtype.ext (d.over0 e))

/-- The first attachment projection followed by the inclusion of `U` into `T`. -/
def firstBase : d.First ⟶ T :=
  d.firstProjection ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[reassoc (attr := simp)] theorem firstBridge_projection :
    d.firstBridge ≫ d.firstProjection = d.bridgeLeft := pushout.inl_desc _ _ _
@[reassoc (attr := simp)] theorem firstEnd_projection :
    d.firstEnd ≫ d.firstProjection = d.p0 := pushout.inr_desc _ _ _
@[reassoc (attr := simp)] theorem firstBridge_base :
    d.firstBridge ≫ d.firstBase = d.bridgeBase := by simp [firstBase]; rfl
@[reassoc (attr := simp)] theorem firstEnd_base :
    d.firstEnd ≫ d.firstBase = d.base0 := by simp [firstBase]; rfl

/-- Attach the overlap restriction `Q1` to the first pushout through the bridge. -/
abbrev secondLeg : d.Q1 ⟶ d.First := d.i1 ≫ d.firstBridge
/-- The iterated pushout attaching the right end `E1` to `First` along `Q1`. -/
abbrev Total : TopCat.{u} := pushout d.secondLeg d.inclusion1
/-- The first attachment inclusion into the total glued space. -/
abbrev totalFirst : d.First ⟶ d.Total := pushout.inl _ _
/-- The right-end inclusion into the total glued space. -/
abbrev totalEnd : d.E1 ⟶ d.Total := pushout.inr _ _
theorem total_isPushout : IsPushout d.secondLeg d.inclusion1 d.totalFirst d.totalEnd :=
  IsPushout.of_hasPushout _ _

/-- The projection of the total glued space to `T`, induced by `firstBase` and `base1` using the
compatibility of the right attachment with the base. -/
def projection : d.Total ⟶ T := pushout.desc d.firstBase d.base1 (by
  rw [secondLeg, Category.assoc, firstBridge_base]
  apply ConcreteCategory.hom_ext
  exact d.over1)

@[reassoc (attr := simp)] theorem totalFirst_projection :
    d.totalFirst ≫ d.projection = d.firstBase := pushout.inl_desc _ _ _
@[reassoc (attr := simp)] theorem totalEnd_projection :
    d.totalEnd ≫ d.projection = d.base1 := pushout.inr_desc _ _ _
@[simp] theorem firstBridge_base_apply (m : d.M) :
    d.firstBase (d.firstBridge m) = (d.q m).1 :=
  ConcreteCategory.congr_hom d.firstBridge_base m
@[simp] theorem firstEnd_base_apply (e : d.E0) :
    d.firstBase (d.firstEnd e) = (d.p0 e).1 :=
  ConcreteCategory.congr_hom d.firstEnd_base e
@[simp] theorem totalFirst_projection_apply (x : d.First) :
    d.projection (d.totalFirst x) = d.firstBase x :=
  ConcreteCategory.congr_hom d.totalFirst_projection x
@[simp] theorem totalEnd_projection_apply (e : d.E1) :
    d.projection (d.totalEnd e) = (d.p1 e).1 :=
  ConcreteCategory.congr_hom d.totalEnd_projection e

theorem firstBase_mem (x : d.First) : d.firstBase x ∈ U := (d.firstProjection x).2

/-- The first attachment is precisely the left open chart of the total. -/
def leftChart (hU : IsOpen U) : d.First ≃ₜ {e : d.Total // d.projection e ∈ U} :=
  OpenAttachment.chartHomeomorph d.base1 U d.total_isPushout d.projection
    d.totalEnd_projection (fun x ↦ by
      rw [totalFirst_projection_apply]
      exact d.firstBase_mem x) hU

@[simp] theorem leftChart_apply (hU : IsOpen U) (x : d.First) :
    (d.leftChart hU x).1 = d.totalFirst x := rfl

/-- The bridge is precisely the right open chart inside the first attachment. -/
def bridgeChart (hV : IsOpen V) : d.M ≃ₜ {e : d.First // d.firstBase e ∈ V} :=
  OpenAttachment.chartHomeomorph d.base0 V d.first_isPushout d.firstBase
    d.firstEnd_base (fun m ↦ by
      rw [firstBridge_base_apply]
      exact (d.q m).2.2) hV

@[simp] theorem bridgeChart_apply (hV : IsOpen V) (m : d.M) :
    (d.bridgeChart hV m).1 = d.firstBridge m := rfl

/-- The projection of the left chart inherits weak lifting from its genuine
fibration by pushing out the given fiberwise deformation. -/
theorem first_weakLifting (s0 : TopCat.CylinderStrongDeformationRetract d.i0)
    (h0 : s0.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
    (hp0 : HomotopyLiftingProperty d.p0.hom) :
    WeakHomotopyLiftingProperty d.firstProjection.hom := by
  apply s0.pushout_weakLifting d.first_isPushout d.firstProjection
  · simp only [firstBridge_projection]
    apply ConcreteCategory.hom_ext
    intro z
    exact Subtype.ext (ConcreteCategory.congr_hom h0 z)
  · simpa only [firstEnd_projection] using hp0.weak

/-- The actual restriction of the total projection over the left open set
has weak lifting. -/
theorem left_weakLifting (hU : IsOpen U)
    (s0 : TopCat.CylinderStrongDeformationRetract d.i0)
    (h0 : s0.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
    (hp0 : HomotopyLiftingProperty d.p0.hom) :
    WeakHomotopyLiftingProperty (baseRestrictionMap d.projection.hom U) := by
  apply (d.first_weakLifting s0 h0 hp0).of_sourceHomeomorph
    (baseRestrictionMap d.projection.hom U) (d.leftChart hU).symm
  ext e
  have hh := d.totalFirst_projection_apply ((d.leftChart hU).symm e)
  have he := congrArg Subtype.val ((d.leftChart hU).apply_symm_apply e)
  change d.totalFirst ((d.leftChart hU).symm e) = e.1 at he
  change d.firstBase ((d.leftChart hU).symm e) = d.projection e.1
  rw [← hh, he]



private def fullSubtypeHomeomorph {X : Type u} [TopologicalSpace X]
    (P : X → Prop) (hP : ∀ x, P x) : X ≃ₜ {x // P x} where
  toFun x := ⟨x, hP x⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_subtype_val

/-- The subspace of the total glued space lying over `V`. -/
abbrev RightChart : TopCat.{u} := TopCat.of {e : d.Total // d.projection e ∈ V}

/-- The bridge map into the actual right open restriction. -/
def rightBridge : d.M ⟶ d.RightChart := TopCat.ofHom
  ⟨fun m ↦ ⟨d.totalFirst (d.firstBridge m), by
    rw [totalFirst_projection_apply, firstBridge_base_apply]
    exact (d.q m).2.2⟩, by fun_prop⟩

/-- The unchanged right fibration maps into the actual right restriction. -/
def rightEnd : d.E1 ⟶ d.RightChart := TopCat.ofHom
  ⟨fun e ↦ ⟨d.totalEnd e, by
    rw [totalEnd_projection_apply]
    exact (d.p1 e).2⟩, by fun_prop⟩

/-- The restricted first corner is identified with the bridge, including
its subspace topology inherited from the actual total pushout. -/
def rightFirstChart (hV : IsOpen V) : d.M ≃ₜ
    OpenPushout.left (g := d.totalFirst) (d.projection ⁻¹' V) :=
  (d.bridgeChart hV).trans (Homeomorph.setCongr (by
    ext x
    change d.firstBase x ∈ V ↔ d.projection (d.totalFirst x) ∈ V
    rw [totalFirst_projection_apply]))

@[simp] theorem rightFirstChart_apply (hV : IsOpen V) (m : d.M) :
    (d.rightFirstChart hV m).1 = d.firstBridge m := rfl

/-- Restriction of the second ordinary pushout to the right open set is
exactly the bridge attached to the unchanged right fibration. -/
theorem right_isPushout (hV : IsOpen V) :
    IsPushout d.i1 d.inclusion1 d.rightBridge d.rightEnd := by
  let es : d.Q1 ≃ₜ OpenPushout.source (i := d.secondLeg) (g := d.totalFirst)
      (d.projection ⁻¹' V) := fullSubtypeHomeomorph _ (fun e ↦ by
        change d.projection (d.totalFirst (d.firstBridge (d.i1 e))) ∈ V
        rw [totalFirst_projection_apply, firstBridge_base_apply]
        exact (d.q (d.i1 e)).2.2)
  let er : d.E1 ≃ₜ OpenPushout.right (j := d.totalEnd) (d.projection ⁻¹' V) :=
    fullSubtypeHomeomorph _ (fun e ↦ by
      change d.projection (d.totalEnd e) ∈ V
      rw [totalEnd_projection_apply]
      exact (d.p1 e).2)
  exact (OpenPushout.isPushout d.total_isPushout (d.projection ⁻¹' V)
    (hV.preimage d.projection.hom.continuous)).of_iso'
      (TopCat.isoOfHomeo es) (TopCat.isoOfHomeo (d.rightFirstChart hV))
      (TopCat.isoOfHomeo er) (Iso.refl _)
      (by ext e; rfl) (by ext e; rfl) (by ext m; rfl) (by ext e; rfl)

/-- The total projection restricted to its right chart, with codomain `V`. -/
def rightProjection : d.RightChart ⟶ TopCat.of V :=
  TopCat.ofHom (baseRestrictionMap d.projection.hom V)

@[reassoc (attr := simp)] theorem rightBridge_projection :
    d.rightBridge ≫ d.rightProjection = d.bridgeRight := by
  ext m
  change d.projection (d.totalFirst (d.firstBridge m)) = (d.q m).1
  rw [totalFirst_projection_apply, firstBridge_base_apply]

@[reassoc (attr := simp)] theorem rightEnd_projection :
    d.rightEnd ≫ d.rightProjection = d.p1 := by
  ext e
  exact d.totalEnd_projection_apply e

/-- The actual restriction of the total projection over the right open set
has weak lifting, from the second primitive fiberwise deformation. -/
theorem right_weakLifting (hV : IsOpen V)
    (s1 : TopCat.CylinderStrongDeformationRetract d.i1)
    (h1 : s1.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
    (hp1 : HomotopyLiftingProperty d.p1.hom) :
    WeakHomotopyLiftingProperty (baseRestrictionMap d.projection.hom V) := by
  apply s1.pushout_weakLifting (d.right_isPushout hV) d.rightProjection
  · simp only [rightBridge_projection]
    apply ConcreteCategory.hom_ext
    intro z
    exact Subtype.ext (ConcreteCategory.congr_hom h1 z)
  · simpa only [rightEnd_projection] using hp1.weak

/-- Two genuine fibrations attached through a two-ended fiberwise
strong-deformation bridge have global weak covering-homotopy lifting.
The only cover hypothesis is an actual subordinate height identifying
the two open sets with its standard overlapping collars. -/
theorem weakLifting (height : C(T, I))
    (hU : U = upperBaseCollar height)
    (hV : V = upperBaseCollar (reflectedHeight height))
    (s0 : TopCat.CylinderStrongDeformationRetract d.i0)
    (s1 : TopCat.CylinderStrongDeformationRetract d.i1)
    (h0 : s0.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
    (h1 : s1.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
    (hp0 : HomotopyLiftingProperty d.p0.hom)
    (hp1 : HomotopyLiftingProperty d.p1.hom) :
    WeakHomotopyLiftingProperty d.projection.hom := by
  have hoU : IsOpen U := by
    rw [hU]
    exact isOpen_lt (continuous_subtype_val.comp height.continuous) continuous_const
  have hoV : IsOpen V := by
    rw [hV]
    exact isOpen_lt (continuous_subtype_val.comp (reflectedHeight height).continuous)
      continuous_const
  apply weakLifting_of_two_collars d.projection.hom height
  · rw [← hU]
    exact d.left_weakLifting hoU s0 h0 hp0
  · rw [← hV]
    exact d.right_weakLifting hoV s1 h1 hp1

/-- Every strict pullback of the actual normalized projection has its
canonical comparison homotopy equivalence to the homotopy pullback. -/
def strictPullbackHomotopyEquiv (height : C(T, I))
    (hU : U = upperBaseCollar height)
    (hV : V = upperBaseCollar (reflectedHeight height))
    (s0 : TopCat.CylinderStrongDeformationRetract d.i0)
    (s1 : TopCat.CylinderStrongDeformationRetract d.i1)
    (h0 : s0.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
    (h1 : s1.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
    (hp0 : HomotopyLiftingProperty d.p0.hom)
    (hp1 : HomotopyLiftingProperty d.p1.hom)
    {S : Type u} [TopologicalSpace S] (a : C(S, T)) :
    ContinuousMap.HomotopyEquiv {z : S × d.Total // d.projection z.2 = a z.1}
      (HomotopyPullback d.projection.hom a) :=
  HomotopyPullback.strictPullbackHomotopyEquivOfWeakLifting d.projection.hom a
    (d.weakLifting height hU hV s0 s1 h0 h1 hp0 hp1)

@[simp] theorem strictPullbackHomotopyEquiv_toFun (height : C(T, I))
    (hU : U = upperBaseCollar height)
    (hV : V = upperBaseCollar (reflectedHeight height))
    (s0 : TopCat.CylinderStrongDeformationRetract d.i0)
    (s1 : TopCat.CylinderStrongDeformationRetract d.i1)
    (h0 : s0.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
    (h1 : s1.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
    (hp0 : HomotopyLiftingProperty d.p0.hom)
    (hp1 : HomotopyLiftingProperty d.p1.hom)
    {S : Type u} [TopologicalSpace S] (a : C(S, T)) :
    (d.strictPullbackHomotopyEquiv height hU hV s0 s1 h0 h1 hp0 hp1 a).toFun =
      HomotopyPullback.strictPullbackInclusion d.projection.hom a := rfl

end Data
end TopCat.OpenGluing
