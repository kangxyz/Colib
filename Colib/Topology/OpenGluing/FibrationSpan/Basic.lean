/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.Basic
public import Colib.Topology.FiberwiseBridge.Basic

/-!
# Normalizing a span of actual fibrations

A common fibration over the overlap maps by actual homotopy equivalences to
both restricted end fibrations. Two ordinary mapping cylinders construct
the bridge and its fiberwise deformations. The resulting actual iterated
pushout has weak covering-homotopy lifting, with no deformation or lifting
conclusion on that pushout among the hypotheses.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/OpenGluing/FibrationSpan/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.FibrationSpan

/-- Two spaces over `U` and `V`, a common overlap space, and compatible maps into their overlap
restrictions. -/
structure Data (T : TopCat.{u}) (U V : Set T) where
  /-- The total space of the map to `U`. -/
  E0 : TopCat.{u}
  /-- The total space of the map to `V`. -/
  E1 : TopCat.{u}
  /-- The common space mapping into both restricted total spaces over the overlap. -/
  R : TopCat.{u}
  /-- The projection from `E0` to the base subset `U`. -/
  p0 : E0 ⟶ TopCat.of U
  /-- The projection from `E1` to the base subset `V`. -/
  p1 : E1 ⟶ TopCat.of V
  /-- The map from `R` to the part of `E0` whose base point also lies in `V`. -/
  k0 : R ⟶ TopCat.of {e : E0 // (p0 e).1 ∈ V}
  /-- The map from `R` to the part of `E1` whose base point also lies in `U`. -/
  k1 : R ⟶ TopCat.of {e : E1 // (p1 e).1 ∈ U}
  /-- The two overlap maps send each point of `R` to the same point of `T`. -/
  over : ∀ r, (p0 (k0 r).1).1 = (p1 (k1 r).1).1

namespace Data
variable {T : TopCat.{u}} {U V : Set T} (d : Data T U V)

/-- The restriction of `E0` to points whose image under `p0` lies in `V`. -/
abbrev Q0 : TopCat.{u} := TopCat.of {e : d.E0 // (d.p0 e).1 ∈ V}
/-- The restriction of `E1` to points whose image under `p1` lies in `U`. -/
abbrev Q1 : TopCat.{u} := TopCat.of {e : d.E1 // (d.p1 e).1 ∈ U}
/-- The restricted left projection, with codomain the intersection `U ∩ V`. -/
def q0 : d.Q0 ⟶ TopCat.of (U ∩ V : Set T) :=
  TopCat.ofHom ⟨fun z ↦ ⟨(d.p0 z.1).1, (d.p0 z.1).2, z.2⟩, by fun_prop⟩
/-- The restricted right projection, with codomain the intersection `U ∩ V`. -/
def q1 : d.Q1 ⟶ TopCat.of (U ∩ V : Set T) :=
  TopCat.ofHom ⟨fun z ↦ ⟨(d.p1 z.1).1, z.2, (d.p1 z.1).2⟩, by fun_prop⟩
theorem square : d.k0 ≫ d.q0 = d.k1 ≫ d.q1 := by
  apply ConcreteCategory.hom_ext
  intro r
  exact Subtype.ext (d.over r)

/-- Restriction of the genuine left fibration to the overlap is still a
fibration, with the exact single-subtype overlap as its base. -/
theorem q0_lifting (hp : HomotopyLiftingProperty d.p0.hom) :
    HomotopyLiftingProperty d.q0.hom := by
  intro A _ a H hzero
  let a' : C(A, d.E0) := ⟨fun x ↦ (a x).1, by fun_prop⟩
  let H' : C(I × A, U) := ⟨fun z ↦ ⟨(H z).1, (H z).2.1⟩, by fun_prop⟩
  obtain ⟨L, hL0, hL⟩ := hp A a' H' (fun x ↦ Subtype.ext (congrArg (fun z : (U ∩ V : Set T) ↦
    z.1) (hzero x)))
  let L' : C(I × A, d.Q0) := ⟨fun z ↦ ⟨L z, by
    have hh := congrArg Subtype.val (hL z.1 z.2)
    change (d.p0 (L z)).1 = (H z).1 at hh
    rw [hh]
    exact (H z).2.2⟩, by fun_prop⟩
  exact ⟨L', fun x ↦ Subtype.ext (hL0 x),
    fun t x ↦ Subtype.ext (congrArg (fun z : U ↦ z.1) (hL t x))⟩

/-- The same exact overlap restriction for the right fibration. -/
theorem q1_lifting (hp : HomotopyLiftingProperty d.p1.hom) :
    HomotopyLiftingProperty d.q1.hom := by
  intro A _ a H hzero
  let a' : C(A, d.E1) := ⟨fun x ↦ (a x).1, by fun_prop⟩
  let H' : C(I × A, V) := ⟨fun z ↦ ⟨(H z).1, (H z).2.2⟩, by fun_prop⟩
  obtain ⟨L, hL0, hL⟩ := hp A a' H' (fun x ↦ Subtype.ext (congrArg (fun z : (U ∩ V : Set T) ↦
    z.1) (hzero x)))
  let L' : C(I × A, d.Q1) := ⟨fun z ↦ ⟨L z, by
    have hh := congrArg Subtype.val (hL z.1 z.2)
    change (d.p1 (L z)).1 = (H z).1 at hh
    rw [hh]
    exact (H z).2.1⟩, by fun_prop⟩
  exact ⟨L', fun x ↦ Subtype.ext (hL0 x),
    fun t x ↦ Subtype.ext (congrArg (fun z : V ↦ z.1) (hL t x))⟩

/-- The mapping cylinder of `k0`, with its target attached at interval parameter `1`. -/
abbrev M0 : TopCat.{u} := pushout (TopCat.ι₁ : d.R ⟶ d.R ⊗ TopCat.I) d.k0
/-- The mapping cylinder of `k1`, with its target attached at interval parameter `1`. -/
abbrev M1 : TopCat.{u} := pushout (TopCat.ι₁ : d.R ⟶ d.R ⊗ TopCat.I) d.k1
/-- The canonical map of `R × I` into the mapping cylinder of `k0`. -/
abbrev line0 : d.R ⊗ TopCat.I ⟶ d.M0 := pushout.inl _ _
/-- The canonical map of `R × I` into the mapping cylinder of `k1`. -/
abbrev line1 : d.R ⊗ TopCat.I ⟶ d.M1 := pushout.inl _ _
/-- The canonical inclusion of the restricted left target `Q0` into its mapping cylinder. -/
abbrev end0 : d.Q0 ⟶ d.M0 := pushout.inr _ _
/-- The canonical inclusion of the restricted right target `Q1` into its mapping cylinder. -/
abbrev end1 : d.Q1 ⟶ d.M1 := pushout.inr _ _
theorem cylinder0 : IsPushout (TopCat.ι₁ : d.R ⟶ d.R ⊗ TopCat.I) d.k0 d.line0 d.end0 :=
  IsPushout.of_hasPushout _ _
theorem cylinder1 : IsPushout (TopCat.ι₁ : d.R ⟶ d.R ⊗ TopCat.I) d.k1 d.line1 d.end1 :=
  IsPushout.of_hasPushout _ _
/-- The copy of `R` at interval parameter `0` in the left mapping cylinder. -/
abbrev start0 : d.R ⟶ d.M0 := TopCat.ι₀ ≫ d.line0
/-- The copy of `R` at interval parameter `0` in the right mapping cylinder. -/
abbrev start1 : d.R ⟶ d.M1 := TopCat.ι₀ ≫ d.line1
/-- The pushout of the two mapping cylinders along their parameter `0` copies of `R`. -/
abbrev Bridge : TopCat.{u} := pushout d.start0 d.start1
/-- The canonical map from the left mapping cylinder into the glued bridge. -/
abbrev bridge0 : d.M0 ⟶ d.Bridge := pushout.inl _ _
/-- The canonical map from the right mapping cylinder into the glued bridge. -/
abbrev bridge1 : d.M1 ⟶ d.Bridge := pushout.inr _ _
theorem bridge_isPushout : IsPushout d.start0 d.start1 d.bridge0 d.bridge1 :=
  IsPushout.of_hasPushout _ _
/-- The projection from the glued bridge to `U ∩ V` induced by `q0` and `q1`. -/
def bridgeProjection : d.Bridge ⟶ TopCat.of (U ∩ V : Set T) :=
  TopCat.FiberwiseBridge.projection d.cylinder0 d.cylinder1 d.bridge_isPushout d.q0 d.q1 d.square

/-- The normalized gluing data are constructed from actual mapping
cylinders, with no chosen global equivalence or deformation. -/
def normalized : OpenGluing.Data T U V where
  E0 := d.E0
  E1 := d.E1
  M := d.Bridge
  p0 := d.p0
  p1 := d.p1
  q := d.bridgeProjection
  i0 := d.end0 ≫ d.bridge0
  i1 := d.end1 ≫ d.bridge1
  over0 e := by
    have hh := ConcreteCategory.congr_hom
      (TopCat.FiberwiseBridge.projection_left d.cylinder0 d.cylinder1 d.bridge_isPushout
        d.q0 d.q1 d.square) (d.end0 e)
    have hh' := ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderProjection_target_assoc d.cylinder0 d.q0) e
    exact congrArg Subtype.val (hh.trans hh')
  over1 e := by
    have hh := ConcreteCategory.congr_hom
      (TopCat.FiberwiseBridge.projection_right d.cylinder0 d.cylinder1 d.bridge_isPushout
        d.q0 d.q1 d.square) (d.end1 e)
    have hh' := ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderProjection_target_assoc d.cylinder1 d.q1) e
    exact congrArg Subtype.val (hh.trans hh')

/-- Every primitive deformation required by normalized gluing is derived
from ordinary equivalences between the three genuine overlap fibrations. -/
theorem normalized_deformations
    (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (E : ContinuousMap.HomotopyEquiv d.R d.Q0) (he : E.toFun = d.k0.hom)
    (F : ContinuousMap.HomotopyEquiv d.R d.Q1) (hf : F.toFun = d.k1.hom) :
    ∃ (s0 : TopCat.CylinderStrongDeformationRetract d.normalized.i0)
      (s1 : TopCat.CylinderStrongDeformationRetract d.normalized.i1),
      s0.H ≫ d.normalized.bridgeBase = fst d.Bridge TopCat.I ≫ d.normalized.bridgeBase ∧
      s1.H ≫ d.normalized.bridgeBase = fst d.Bridge TopCat.I ≫ d.normalized.bridgeBase := by
  have hR' : HomotopyLiftingProperty (d.k1 ≫ d.q1).hom := by rw [← d.square]; exact hR
  let EF := fiberwiseEquivOfFibrationHomotopyEquiv (d.k0 ≫ d.q0).hom d.q0.hom
    hR (d.q0_lifting hp0) E (by rw [he]; rfl)
  let FF := fiberwiseEquivOfFibrationHomotopyEquiv (d.k1 ≫ d.q1).hom d.q1.hom
    hR' (d.q1_lifting hp1) F (by rw [hf]; rfl)
  obtain ⟨s0, s1, hs0, hs1⟩ := TopCat.FiberwiseBridge.exists_strongDeformationRetracts
    d.cylinder0 d.cylinder1 d.bridge_isPushout d.q0 d.q1 d.square EF
    ((fiberwiseEquivOfFibrationHomotopyEquiv_toMap _ _ _ _ _ _).trans he) FF
    ((fiberwiseEquivOfFibrationHomotopyEquiv_toMap _ _ _ _ _ _).trans hf)
  refine ⟨s0, s1, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro z
    exact congrArg Subtype.val (ConcreteCategory.congr_hom hs0 z)
  · apply ConcreteCategory.hom_ext
    intro z
    exact congrArg Subtype.val (ConcreteCategory.congr_hom hs1 z)

/-- Actual global weak lifting for the normalized span. All geometric
inverse data and all local lifting statements have been constructed. -/
theorem weakLifting (height : C(T, I))
    (hU : U = upperBaseCollar height) (hV : V = upperBaseCollar (reflectedHeight height))
    (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (E : ContinuousMap.HomotopyEquiv d.R d.Q0) (he : E.toFun = d.k0.hom)
    (F : ContinuousMap.HomotopyEquiv d.R d.Q1) (hf : F.toFun = d.k1.hom) :
    WeakHomotopyLiftingProperty d.normalized.projection.hom := by
  obtain ⟨s0, s1, hs0, hs1⟩ := d.normalized_deformations hp0 hp1 hR E he F hf
  exact d.normalized.weakLifting height hU hV s0 s1 hs0 hs1 hp0 hp1

/-- The actual normalized projection makes every ordinary pullback square
homotopy cartesian, with exactly the canonical comparison map. -/
def strictPullbackHomotopyEquiv (height : C(T, I))
    (hU : U = upperBaseCollar height) (hV : V = upperBaseCollar (reflectedHeight height))
    (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (E : ContinuousMap.HomotopyEquiv d.R d.Q0) (he : E.toFun = d.k0.hom)
    (F : ContinuousMap.HomotopyEquiv d.R d.Q1) (hf : F.toFun = d.k1.hom)
    {S : Type u} [TopologicalSpace S] (a : C(S, T)) :
    ContinuousMap.HomotopyEquiv {z : S × d.normalized.Total // d.normalized.projection z.2 = a z.1}
      (HomotopyPullback d.normalized.projection.hom a) :=
  HomotopyPullback.strictPullbackHomotopyEquivOfWeakLifting d.normalized.projection.hom a
    (d.weakLifting height hU hV hp0 hp1 hR E he F hf)

@[simp] theorem strictPullbackHomotopyEquiv_toFun (height : C(T, I))
    (hU : U = upperBaseCollar height) (hV : V = upperBaseCollar (reflectedHeight height))
    (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (E : ContinuousMap.HomotopyEquiv d.R d.Q0) (he : E.toFun = d.k0.hom)
    (F : ContinuousMap.HomotopyEquiv d.R d.Q1) (hf : F.toFun = d.k1.hom)
    {S : Type u} [TopologicalSpace S] (a : C(S, T)) :
    (d.strictPullbackHomotopyEquiv height hU hV hp0 hp1 hR E he F hf a).toFun =
      HomotopyPullback.strictPullbackInclusion d.normalized.projection.hom a := rfl

end Data
end TopCat.FibrationSpan
