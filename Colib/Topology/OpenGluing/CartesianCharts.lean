/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.FibrationSpan.Basic

/-!
# Canonical endpoint chart comparisons for normalized gluing

The unchanged endpoint fibrations map by homotopy equivalences into the
actual open charts of the normalized total. Composing these equivalences
with the canonical strict-pullback comparison proves that the endpoint
chart squares are homotopy cartesian. The forward maps remain exactly the
canonical constant-path comparisons.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/OpenGluing/CartesianCharts.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyPullback

/-- The inverse image of a subspace is its actual strict pullback, with
both inherited topologies respected. -/
def preimageStrictPullbackHomeomorph {X B : Type u}
    [TopologicalSpace X] [TopologicalSpace B] (p : C(X, B)) (U : Set B) :
    {x : X // p x ∈ U} ≃ₜ {z : U × X // p z.2 = z.1.1} where
  toFun x := ⟨(⟨p x.1, x.2⟩, x.1), rfl⟩
  invFun z := ⟨z.1.2, by rw [z.2]; exact z.1.1.2⟩
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext (Subtype.ext z.2) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Topology.HomotopyPullback

namespace TopCat
namespace OpenGluing.Data
variable {T : TopCat.{u}} {U V : Set T} (d : OpenGluing.Data T U V)

/-- Inclusion of the original left endpoint into the normalized total. -/
abbrev totalLeft : d.E0 ⟶ d.Total := d.firstEnd ≫ d.totalFirst

@[reassoc] theorem totalLeft_projection :
    d.totalLeft ≫ d.projection = d.base0 := by
  simp only [totalLeft, Category.assoc, totalFirst_projection, firstEnd_base]

/-- Inclusion of the left open set into the covered base. -/
def leftBaseInclusion (_d : OpenGluing.Data T U V) : C(U, T) := ⟨Subtype.val,
    continuous_subtype_val⟩

/-- Inclusion of the right open set into the covered base. -/
def rightBaseInclusion (_d : OpenGluing.Data T U V) : C(V, T) := ⟨Subtype.val,
    continuous_subtype_val⟩

theorem left_square :
    d.projection.hom.comp d.totalLeft.hom = d.leftBaseInclusion.comp d.p0.hom :=
  congrArg TopCat.Hom.hom d.totalLeft_projection

theorem right_square :
    d.projection.hom.comp d.totalEnd.hom = d.rightBaseInclusion.comp d.p1.hom :=
  congrArg TopCat.Hom.hom d.totalEnd_projection

/-- The canonical constant-path comparison of the left endpoint chart
square into the actual path-space homotopy pullback. -/
def leftComparison : C(d.E0, HomotopyPullback d.projection.hom d.leftBaseInclusion) :=
  HomotopyPullback.comparison _ _ d.p0.hom d.totalLeft.hom d.left_square

/-- The canonical constant-path comparison of the right endpoint chart
square into the actual path-space homotopy pullback. -/
def rightComparison : C(d.E1, HomotopyPullback d.projection.hom d.rightBaseInclusion) :=
  HomotopyPullback.comparison _ _ d.p1.hom d.totalEnd.hom d.right_square

/-- The left endpoint deformation, actual open chart, and strict pullback
comparison give the canonical homotopy-cartesian left chart square. -/
def leftComparisonHomotopyEquiv (hU : IsOpen U)
    (s0 : TopCat.CylinderStrongDeformationRetract d.i0)
    (hp : WeakHomotopyLiftingProperty d.projection.hom) :
    ContinuousMap.HomotopyEquiv d.E0
      (HomotopyPullback d.projection.hom d.leftBaseInclusion) :=
  ((s0.pushout d.first_isPushout).toHomotopyEquiv.trans
    (d.leftChart hU).toHomotopyEquiv).trans
      ((HomotopyPullback.preimageStrictPullbackHomeomorph d.projection.hom U).toHomotopyEquiv.trans
        (HomotopyPullback.strictPullbackHomotopyEquivOfWeakLifting
          d.projection.hom d.leftBaseInclusion hp))

@[simp] theorem leftComparisonHomotopyEquiv_toFun (hU : IsOpen U)
    (s0 : TopCat.CylinderStrongDeformationRetract d.i0)
    (hp : WeakHomotopyLiftingProperty d.projection.hom) :
    (d.leftComparisonHomotopyEquiv hU s0 hp).toFun = d.leftComparison := by
  ext x
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact ConcreteCategory.congr_hom d.totalLeft_projection x
  · apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact ConcreteCategory.congr_hom d.totalLeft_projection x

/-- The right endpoint deformation is pushed out directly into the actual
right restriction, then compared with the path-space pullback. -/
def rightComparisonHomotopyEquiv (hV : IsOpen V)
    (s1 : TopCat.CylinderStrongDeformationRetract d.i1)
    (hp : WeakHomotopyLiftingProperty d.projection.hom) :
    ContinuousMap.HomotopyEquiv d.E1
      (HomotopyPullback d.projection.hom d.rightBaseInclusion) :=
  (s1.pushout (d.right_isPushout hV)).toHomotopyEquiv.trans
    ((HomotopyPullback.preimageStrictPullbackHomeomorph d.projection.hom V).toHomotopyEquiv.trans
      (HomotopyPullback.strictPullbackHomotopyEquivOfWeakLifting
        d.projection.hom d.rightBaseInclusion hp))

@[simp] theorem rightComparisonHomotopyEquiv_toFun (hV : IsOpen V)
    (s1 : TopCat.CylinderStrongDeformationRetract d.i1)
    (hp : WeakHomotopyLiftingProperty d.projection.hom) :
    (d.rightComparisonHomotopyEquiv hV s1 hp).toFun = d.rightComparison := by
  ext x
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact d.totalEnd_projection_apply x
  · apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact d.totalEnd_projection_apply x

section Global
variable (height : C(T, I))
  (hU : U = upperBaseCollar height)
  (hV : V = upperBaseCollar (reflectedHeight height))
  (s0 : TopCat.CylinderStrongDeformationRetract d.i0)
  (s1 : TopCat.CylinderStrongDeformationRetract d.i1)
  (h0 : s0.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
  (h1 : s1.H ≫ d.bridgeBase = fst d.M TopCat.I ≫ d.bridgeBase)
  (hp0 : HomotopyLiftingProperty d.p0.hom)
  (hp1 : HomotopyLiftingProperty d.p1.hom)

/-- The canonical left endpoint chart square is homotopy cartesian,
using only the primitive endpoint fibrations and bridge deformations. -/
def leftChartHomotopyEquiv : ContinuousMap.HomotopyEquiv d.E0
    (HomotopyPullback d.projection.hom d.leftBaseInclusion) :=
  d.leftComparisonHomotopyEquiv (by
    rw [hU]
    exact isOpen_lt (continuous_subtype_val.comp height.continuous) continuous_const)
      s0 (d.weakLifting height hU hV s0 s1 h0 h1 hp0 hp1)

@[simp] theorem leftChartHomotopyEquiv_toFun :
    (d.leftChartHomotopyEquiv height hU hV s0 s1 h0 h1 hp0 hp1).toFun =
      HomotopyPullback.comparison d.projection.hom d.leftBaseInclusion
        d.p0.hom d.totalLeft.hom d.left_square :=
  d.leftComparisonHomotopyEquiv_toFun _ _ _

/-- The canonical right endpoint chart square is homotopy cartesian,
using only the primitive endpoint fibrations and bridge deformations. -/
def rightChartHomotopyEquiv : ContinuousMap.HomotopyEquiv d.E1
    (HomotopyPullback d.projection.hom d.rightBaseInclusion) :=
  d.rightComparisonHomotopyEquiv (by
    rw [hV]
    exact isOpen_lt (continuous_subtype_val.comp (reflectedHeight height).continuous)
      continuous_const)
      s1 (d.weakLifting height hU hV s0 s1 h0 h1 hp0 hp1)

@[simp] theorem rightChartHomotopyEquiv_toFun :
    (d.rightChartHomotopyEquiv height hU hV s0 s1 h0 h1 hp0 hp1).toFun =
      HomotopyPullback.comparison d.projection.hom d.rightBaseInclusion
        d.p1.hom d.totalEnd.hom d.right_square :=
  d.rightComparisonHomotopyEquiv_toFun _ _ _

end Global
end OpenGluing.Data

namespace FibrationSpan.Data
variable {T : TopCat.{u}} {U V : Set T} (d : FibrationSpan.Data T U V)
  (height : C(T, I))
  (hU : U = upperBaseCollar height)
  (hV : V = upperBaseCollar (reflectedHeight height))
  (hp0 : HomotopyLiftingProperty d.p0.hom)
  (hp1 : HomotopyLiftingProperty d.p1.hom)
  (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
  (E : ContinuousMap.HomotopyEquiv d.R d.Q0) (he : E.toFun = d.k0.hom)
  (F : ContinuousMap.HomotopyEquiv d.R d.Q1) (hf : F.toFun = d.k1.hom)

/-- Ordinary homotopy equivalences of genuine overlap fibrations give the
canonical left endpoint chart equivalence of the constructed normalization.
The necessary fiberwise bridge deformations are derived, not assumed. -/
def leftChartHomotopyEquiv : ContinuousMap.HomotopyEquiv d.E0
    (HomotopyPullback d.normalized.projection.hom d.normalized.leftBaseInclusion) :=
  let hs := d.normalized_deformations hp0 hp1 hR E he F hf
  d.normalized.leftChartHomotopyEquiv height hU hV hs.choose hs.choose_spec.choose
    hs.choose_spec.choose_spec.1 hs.choose_spec.choose_spec.2 hp0 hp1

@[simp] theorem leftChartHomotopyEquiv_toFun :
    (d.leftChartHomotopyEquiv height hU hV hp0 hp1 hR E he F hf).toFun =
      HomotopyPullback.comparison d.normalized.projection.hom d.normalized.leftBaseInclusion
        d.p0.hom d.normalized.totalLeft.hom d.normalized.left_square :=
  by
    let hs := d.normalized_deformations hp0 hp1 hR E he F hf
    exact d.normalized.leftChartHomotopyEquiv_toFun height hU hV hs.choose hs.choose_spec.choose
      hs.choose_spec.choose_spec.1 hs.choose_spec.choose_spec.2 hp0 hp1

/-- The same construction on the right endpoint, with exactly its
canonical map to the path-space homotopy pullback. -/
def rightChartHomotopyEquiv : ContinuousMap.HomotopyEquiv d.E1
    (HomotopyPullback d.normalized.projection.hom d.normalized.rightBaseInclusion) :=
  let hs := d.normalized_deformations hp0 hp1 hR E he F hf
  d.normalized.rightChartHomotopyEquiv height hU hV hs.choose hs.choose_spec.choose
    hs.choose_spec.choose_spec.1 hs.choose_spec.choose_spec.2 hp0 hp1

@[simp] theorem rightChartHomotopyEquiv_toFun :
    (d.rightChartHomotopyEquiv height hU hV hp0 hp1 hR E he F hf).toFun =
      HomotopyPullback.comparison d.normalized.projection.hom d.normalized.rightBaseInclusion
        d.p1.hom d.normalized.totalEnd.hom d.normalized.right_square :=
  by
    let hs := d.normalized_deformations hp0 hp1 hR E he F hf
    exact d.normalized.rightChartHomotopyEquiv_toFun height hU hV hs.choose hs.choose_spec.choose
      hs.choose_spec.choose_spec.1 hs.choose_spec.choose_spec.2 hp0 hp1

end FibrationSpan.Data
end TopCat
