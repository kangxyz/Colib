/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.FibrationSpan.Pushout
public import Colib.Topology.DoubleMappingCylinder.Subdivision

/-!
# Actual homotopy-cartesian gluing over two open sets

The ordinary double mapping cylinder of a span of overlap fibrations has
weak covering-homotopy lifting over the covered space. Normalization,
local deformations, pushout reassociation, and interval subdivision are
all constructed. The conclusion concerns the ordinary TopCat double
cylinder and its exact collapse, not an assumed normalized replacement.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/OpenGluing/FibrationSpan/DoubleCylinder.lean` at
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
namespace TopCat.FibrationSpan.Data
variable {T : TopCat.{u}} {U V : Set T} (d : Data T U V)

@[reassoc] theorem totalLine0_projection :
    d.totalLine0 ≫ d.normalized.projection =
      fst d.R TopCat.I ≫ d.leftLeg ≫ d.normalized.base0 := by
  simp only [totalLine0, Category.assoc, OpenGluing.Data.totalFirst_projection,
    OpenGluing.Data.firstBridge_base]
  apply ConcreteCategory.hom_ext
  intro z
  have hh := ConcreteCategory.congr_hom
    (TopCat.FiberwiseBridge.projection_left d.cylinder0 d.cylinder1 d.bridge_isPushout
      d.q0 d.q1 d.square) (d.line0 z)
  have hk := ConcreteCategory.congr_hom
    (TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc d.cylinder0 d.q0) z
  exact congrArg Subtype.val (hh.trans hk)

@[reassoc] theorem totalLine1_projection :
    d.totalLine1 ≫ d.normalized.projection =
      fst d.R TopCat.I ≫ d.leftLeg ≫ d.normalized.base0 := by
  simp only [totalLine1, Category.assoc, OpenGluing.Data.totalFirst_projection,
    OpenGluing.Data.firstBridge_base]
  apply ConcreteCategory.hom_ext
  intro z
  have hh := ConcreteCategory.congr_hom
    (TopCat.FiberwiseBridge.projection_right d.cylinder0 d.cylinder1 d.bridge_isPushout
      d.q0 d.q1 d.square) (d.line1 z)
  have hk := ConcreteCategory.congr_hom
    (TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc d.cylinder1 d.q1) z
  exact (congrArg Subtype.val (hh.trans hk)).trans (d.over z.1).symm

@[reassoc] theorem totalLeft_projection :
    d.totalLeft ≫ d.normalized.projection = d.normalized.base0 := by
  simp only [totalLeft, Category.assoc, OpenGluing.Data.totalFirst_projection,
    OpenGluing.Data.firstEnd_base]
@[reassoc] theorem totalRight_projection :
    d.totalRight ≫ d.normalized.projection = d.normalized.base1 :=
  d.normalized.totalEnd_projection

variable {D : TopCat.{u}} {l : d.R ⊗ TopCat.I ⟶ D}
  {e : TopCat.of (d.E0 ⊕ d.E1) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints d.R) (DoubleCylinder.endMap d.leftLeg d.rightLeg) l e)

/-- The actual collapse to the space covered by the two base sets. -/
def collapse : D ⟶ T := sq.desc
  (fst d.R TopCat.I ≫ d.leftLeg ≫ d.normalized.base0)
  (TopCat.ofHom ⟨Sum.elim d.normalized.base0 d.normalized.base1,
    continuous_sum_dom.mpr ⟨d.normalized.base0.hom.continuous, d.normalized.base1.hom.continuous⟩⟩)
  (by
    apply ConcreteCategory.hom_ext
    intro r
    cases r with
    | inl r => rfl
    | inr r => exact d.over r)

@[reassoc (attr := simp)] theorem collapse_cylinder :
    l ≫ d.collapse sq = fst d.R TopCat.I ≫ d.leftLeg ≫ d.normalized.base0 :=
  sq.inl_desc _ _ _

@[reassoc (attr := simp)] theorem collapse_left :
    DoubleCylinder.Subdivision.leftEnd (e := e) ≫ d.collapse sq = d.normalized.base0 := by
  apply ConcreteCategory.hom_ext
  intro x
  exact ConcreteCategory.congr_hom (sq.inr_desc _ _ _) (Sum.inl x)

@[reassoc (attr := simp)] theorem collapse_right :
    DoubleCylinder.Subdivision.rightEnd (e := e) ≫ d.collapse sq = d.normalized.base1 := by
  apply ConcreteCategory.hom_ext
  intro x
  exact ConcreteCategory.congr_hom (sq.inr_desc _ _ _) (Sum.inr x)

/-- Reassociation and subdivision give a genuine homeomorphism between
the ordinary double cylinder and the explicitly normalized total. -/
def normalizedHomeomorph : D ≃ₜ d.normalized.Total :=
  DoubleCylinder.Subdivision.homeomorph sq d.fullCylinder0 d.fullCylinder1 d.full_isPushout

/-- The homeomorphism respects the actual base collapse exactly. -/
theorem normalizedHomeomorph_over :
    d.normalized.projection.hom.comp (d.normalizedHomeomorph sq : C(D, d.normalized.Total)) =
      (d.collapse sq).hom := by
  apply congrArg TopCat.Hom.hom
  apply DoubleCylinder.Subdivision.forward_over sq d.fullCylinder0 d.fullCylinder1 d.full_isPushout
    (d.collapse sq) d.normalized.projection (d.leftLeg ≫ d.normalized.base0)
  · exact d.collapse_cylinder sq
  · rw [← Category.assoc, show d.fullLine0 ≫ d.fullMap0 = d.totalLine0 from pushout.inl_desc _ _ _]
    exact d.totalLine0_projection
  · rw [← Category.assoc, show d.fullLine1 ≫ d.fullMap1 = d.totalLine1 from pushout.inl_desc _ _ _]
    exact d.totalLine1_projection
  · rw [← Category.assoc, show d.fullEnd0 ≫ d.fullMap0 = d.totalLeft from pushout.inr_desc _ _ _,
      totalLeft_projection, collapse_left]
  · rw [← Category.assoc, show d.fullEnd1 ≫ d.fullMap1 = d.totalRight from pushout.inr_desc _ _ _,
      totalRight_projection, collapse_right]

/-- The ordinary double-cylinder collapse of equivalent overlap
fibrations satisfies actual global weak covering-homotopy lifting. -/
theorem collapse_weakLifting (height : C(T, I))
    (hU : U = upperBaseCollar height) (hV : V = upperBaseCollar (reflectedHeight height))
    (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (E : ContinuousMap.HomotopyEquiv d.R d.Q0) (he : E.toFun = d.k0.hom)
    (F : ContinuousMap.HomotopyEquiv d.R d.Q1) (hf : F.toFun = d.k1.hom) :
    WeakHomotopyLiftingProperty (d.collapse sq).hom :=
  (d.weakLifting height hU hV hp0 hp1 hR E he F hf).of_sourceHomeomorph
    (d.collapse sq).hom (d.normalizedHomeomorph sq) (d.normalizedHomeomorph_over sq)

/-- Every actual strict pullback of that ordinary double cylinder is
homotopy cartesian via its canonical constant-path comparison. -/
def collapsePullbackHomotopyEquiv (height : C(T, I))
    (hU : U = upperBaseCollar height) (hV : V = upperBaseCollar (reflectedHeight height))
    (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (E : ContinuousMap.HomotopyEquiv d.R d.Q0) (he : E.toFun = d.k0.hom)
    (F : ContinuousMap.HomotopyEquiv d.R d.Q1) (hf : F.toFun = d.k1.hom)
    {S : Type u} [TopologicalSpace S] (a : C(S, T)) :
    ContinuousMap.HomotopyEquiv {z : S × D // d.collapse sq z.2 = a z.1}
      (HomotopyPullback (d.collapse sq).hom a) :=
  HomotopyPullback.strictPullbackHomotopyEquivOfWeakLifting _ _
    (d.collapse_weakLifting sq height hU hV hp0 hp1 hR E he F hf)

end TopCat.FibrationSpan.Data
