/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.FibrationSpan.Basic

/-! The normalized iterated pushout has exactly the universal property of
a subdivided double mapping cylinder on its original three-term span. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/OpenGluing/FibrationSpan/Pushout.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.FibrationSpan.Data
variable {T : TopCat.{u}} {U V : Set T} (d : Data T U V)

/-- The original overlap map into `E0`, obtained by forgetting the restriction in `k0`. -/
abbrev leftLeg : d.R ⟶ d.E0 := d.k0 ≫ d.normalized.inclusion0
/-- The original overlap map into `E1`, obtained by forgetting the restriction in `k1`. -/
abbrev rightLeg : d.R ⟶ d.E1 := d.k1 ≫ d.normalized.inclusion1
/-- The map of the left cylinder `R × I` into the normalized iterated pushout. -/
abbrev totalLine0 : d.R ⊗ TopCat.I ⟶ d.normalized.Total :=
  d.line0 ≫ d.bridge0 ≫ d.normalized.firstBridge ≫ d.normalized.totalFirst
/-- The map of the right cylinder `R × I` into the normalized iterated pushout. -/
abbrev totalLine1 : d.R ⊗ TopCat.I ⟶ d.normalized.Total :=
  d.line1 ≫ d.bridge1 ≫ d.normalized.firstBridge ≫ d.normalized.totalFirst
/-- The canonical map of `E0` into the normalized iterated pushout. -/
abbrev totalLeft : d.E0 ⟶ d.normalized.Total := d.normalized.firstEnd ≫ d.normalized.totalFirst
/-- The canonical map of `E1` into the normalized iterated pushout. -/
abbrev totalRight : d.E1 ⟶ d.normalized.Total := d.normalized.totalEnd

@[reassoc] theorem bridgeEnd0_total :
    d.end0 ≫ d.bridge0 ≫ d.normalized.firstBridge ≫ d.normalized.totalFirst =
      d.normalized.inclusion0 ≫ d.totalLeft := by
  have h := congrArg (fun k ↦ k ≫ d.normalized.totalFirst) d.normalized.first_isPushout.w
  change ((d.end0 ≫ d.bridge0) ≫ d.normalized.firstBridge) ≫ d.normalized.totalFirst = _ at h
  simpa only [Category.assoc] using h
@[reassoc] theorem bridgeEnd1_total :
    d.end1 ≫ d.bridge1 ≫ d.normalized.firstBridge ≫ d.normalized.totalFirst =
      d.normalized.inclusion1 ≫ d.totalRight := by
  have h := d.normalized.total_isPushout.w
  change ((d.end1 ≫ d.bridge1) ≫ d.normalized.firstBridge) ≫ d.normalized.totalFirst = _ at h
  simpa only [Category.assoc] using h

theorem totalLine0_one : TopCat.ι₁ ≫ d.totalLine0 = d.leftLeg ≫ d.totalLeft := by
  change TopCat.ι₁ ≫ d.line0 ≫ _ = _
  rw [← Category.assoc, d.cylinder0.w, Category.assoc, bridgeEnd0_total]
  rfl

theorem totalLine1_one : TopCat.ι₁ ≫ d.totalLine1 = d.rightLeg ≫ d.totalRight := by
  change TopCat.ι₁ ≫ d.line1 ≫ _ = _
  rw [← Category.assoc, d.cylinder1.w, Category.assoc, bridgeEnd1_total]
  rfl

theorem totalLine_zero : TopCat.ι₀ ≫ d.totalLine0 = TopCat.ι₀ ≫ d.totalLine1 := by
  change TopCat.ι₀ ≫ d.line0 ≫ _ = TopCat.ι₀ ≫ d.line1 ≫ _
  simpa only [Category.assoc] using congrArg
    (fun h ↦ h ≫ d.normalized.firstBridge ≫ d.normalized.totalFirst) d.bridge_isPushout.w

section Desc
variable {Z : TopCat.{u}} (a0 a1 : d.R ⊗ TopCat.I ⟶ Z) (b0 : d.E0 ⟶ Z) (b1 : d.E1 ⟶ Z)
  (h0 : TopCat.ι₁ ≫ a0 = d.leftLeg ≫ b0)
  (h1 : TopCat.ι₁ ≫ a1 = d.rightLeg ≫ b1)
  (hs : TopCat.ι₀ ≫ a0 = TopCat.ι₀ ≫ a1)

/-- The map from the cylinder bridge to `Z` induced by `a0`, `a1`, and the restricted endpoint
maps, with the supplied endpoint and source compatibilities. -/
def foldBridge : d.Bridge ⟶ Z := pushout.desc
  (pushout.desc a0 (d.normalized.inclusion0 ≫ b0) h0)
  (pushout.desc a1 (d.normalized.inclusion1 ≫ b1) h1) (by
    simp only [start0, start1, Category.assoc, pushout.inl_desc]
    exact hs)

@[reassoc (attr := simp)] theorem bridge0_foldBridge :
    d.bridge0 ≫ foldBridge d a0 a1 b0 b1 h0 h1 hs =
      pushout.desc a0 (d.normalized.inclusion0 ≫ b0) h0 := pushout.inl_desc _ _ _
@[reassoc (attr := simp)] theorem bridge1_foldBridge :
    d.bridge1 ≫ foldBridge d a0 a1 b0 b1 h0 h1 hs =
      pushout.desc a1 (d.normalized.inclusion1 ≫ b1) h1 := pushout.inr_desc _ _ _

/-- Extend the compatible bridge map to the first attachment by the given map `b0 : E0 ⟶ Z`. -/
def foldFirst : d.normalized.First ⟶ Z := pushout.desc (foldBridge d a0 a1 b0 b1 h0 h1 hs) b0 (by
  change (d.end0 ≫ d.bridge0) ≫ foldBridge d a0 a1 b0 b1 h0 h1 hs = _
  rw [Category.assoc, bridge0_foldBridge]
  exact pushout.inr_desc _ _ _)

/-- The map from the normalized total to `Z` induced by two compatible cylinder maps and the two
endpoint maps. -/
def fold : d.normalized.Total ⟶ Z := pushout.desc (foldFirst d a0 a1 b0 b1 h0 h1 hs) b1 (by
  change ((d.end1 ≫ d.bridge1) ≫ d.normalized.firstBridge) ≫ foldFirst d a0 a1 b0 b1 h0 h1 hs = _
  simp only [Category.assoc, foldFirst, OpenGluing.Data.firstBridge, pushout.inl_desc,
    bridge1_foldBridge]
  exact pushout.inr_desc _ _ _)

/-- The fold restricts to the prescribed cylinder map along the normalized bridges. -/
@[reassoc (attr := simp)] theorem line0_bridge_fold :
    d.line0 ≫ d.bridge0 ≫ d.normalized.firstBridge ≫ d.normalized.totalFirst ≫
      fold d a0 a1 b0 b1 h0 h1 hs = a0 := by
  simp only [fold, foldFirst, OpenGluing.Data.totalFirst,
    OpenGluing.Data.firstBridge, pushout.inl_desc, bridge0_foldBridge, line0]

/-- The fold restricts to the prescribed cylinder map along the normalized bridges. -/
@[reassoc (attr := simp)] theorem line1_bridge_fold :
    d.line1 ≫ d.bridge1 ≫ d.normalized.firstBridge ≫ d.normalized.totalFirst ≫
      fold d a0 a1 b0 b1 h0 h1 hs = a1 := by
  simp only [fold, foldFirst, OpenGluing.Data.totalFirst,
    OpenGluing.Data.firstBridge, pushout.inl_desc, bridge1_foldBridge, line1]

@[reassoc (attr := simp)] theorem totalLeft_fold :
    d.normalized.firstEnd ≫ d.normalized.totalFirst ≫ fold d a0 a1 b0 b1 h0 h1 hs =
      b0 := by
  simp only [fold, foldFirst, OpenGluing.Data.totalFirst,
    OpenGluing.Data.firstEnd, pushout.inl_desc, pushout.inr_desc]
@[reassoc (attr := simp)] theorem totalRight_fold : d.totalRight ≫ fold d a0 a1 b0 b1 h0 h1 hs = b1
  :=
  pushout.inr_desc _ _ _
end Desc

/-- The two actual cylinder maps and both endpoint maps jointly determine
maps from the normalized total. -/
theorem total_hom_ext {Z : TopCat.{u}} {a b : d.normalized.Total ⟶ Z}
    (h0 : d.totalLine0 ≫ a = d.totalLine0 ≫ b)
    (h1 : d.totalLine1 ≫ a = d.totalLine1 ≫ b)
    (hl : d.totalLeft ≫ a = d.totalLeft ≫ b)
    (hr : d.totalRight ≫ a = d.totalRight ≫ b) : a = b := by
  apply d.normalized.total_isPushout.hom_ext
  · apply d.normalized.first_isPushout.hom_ext
    · apply d.bridge_isPushout.hom_ext
      · apply d.cylinder0.hom_ext
        · simpa only [Category.assoc] using h0
        · simpa only [Category.assoc, bridgeEnd0_total_assoc] using
            congrArg (fun k ↦ d.normalized.inclusion0 ≫ k) hl
      · apply d.cylinder1.hom_ext
        · simpa only [Category.assoc] using h1
        · simpa only [Category.assoc, bridgeEnd1_total_assoc] using
            congrArg (fun k ↦ d.normalized.inclusion1 ≫ k) hr
    · simpa only [Category.assoc] using hl
  · exact hr

/-- The mapping cylinder of the full left leg `R ⟶ E0`, attached at interval parameter `1`. -/
abbrev FullM0 : TopCat.{u} := pushout (TopCat.ι₁ : d.R ⟶ d.R ⊗ TopCat.I) d.leftLeg
/-- The mapping cylinder of the full right leg `R ⟶ E1`, attached at interval parameter `1`. -/
abbrev FullM1 : TopCat.{u} := pushout (TopCat.ι₁ : d.R ⟶ d.R ⊗ TopCat.I) d.rightLeg
/-- The canonical cylinder map `R × I ⟶ FullM0`. -/
abbrev fullLine0 : d.R ⊗ TopCat.I ⟶ d.FullM0 := pushout.inl _ _
/-- The canonical cylinder map `R × I ⟶ FullM1`. -/
abbrev fullLine1 : d.R ⊗ TopCat.I ⟶ d.FullM1 := pushout.inl _ _
/-- The canonical target inclusion `E0 ⟶ FullM0`. -/
abbrev fullEnd0 : d.E0 ⟶ d.FullM0 := pushout.inr _ _
/-- The canonical target inclusion `E1 ⟶ FullM1`. -/
abbrev fullEnd1 : d.E1 ⟶ d.FullM1 := pushout.inr _ _
theorem fullCylinder0 : IsPushout (TopCat.ι₁ : d.R ⟶ d.R ⊗ TopCat.I) d.leftLeg d.fullLine0
  d.fullEnd0 :=
  IsPushout.of_hasPushout _ _
theorem fullCylinder1 : IsPushout (TopCat.ι₁ : d.R ⟶ d.R ⊗ TopCat.I) d.rightLeg d.fullLine1
  d.fullEnd1 :=
  IsPushout.of_hasPushout _ _
/-- The map from the full left mapping cylinder to the normalized total induced by `totalLine0`
and `totalLeft`. -/
def fullMap0 : d.FullM0 ⟶ d.normalized.Total := pushout.desc d.totalLine0 d.totalLeft
  d.totalLine0_one
/-- The map from the full right mapping cylinder to the normalized total induced by `totalLine1`
and `totalRight`. -/
def fullMap1 : d.FullM1 ⟶ d.normalized.Total := pushout.desc d.totalLine1 d.totalRight
  d.totalLine1_one

theorem full_square : (TopCat.ι₀ ≫ d.fullLine0) ≫ d.fullMap0 =
    (TopCat.ι₀ ≫ d.fullLine1) ≫ d.fullMap1 := by
  simp only [Category.assoc, fullMap0, fullMap1, fullLine0, fullLine1, pushout.inl_desc]
  exact d.totalLine_zero

/-- Reassociation removes the intermediate overlap targets completely:
the normalized total is an actual split double cylinder on the original
span into the two end spaces. -/
theorem full_isPushout : IsPushout (TopCat.ι₀ ≫ d.fullLine0) (TopCat.ι₀ ≫ d.fullLine1)
    d.fullMap0 d.fullMap1 := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ d.full_square)
  apply PushoutCocone.IsColimit.mk d.full_square
    (fun s ↦ fold d (d.fullLine0 ≫ s.inl) (d.fullLine1 ≫ s.inr)
      (d.fullEnd0 ≫ s.inl) (d.fullEnd1 ≫ s.inr)
      (by rw [← Category.assoc, d.fullCylinder0.w, Category.assoc])
      (by rw [← Category.assoc, d.fullCylinder1.w, Category.assoc])
      (by simpa only [Category.assoc] using s.condition))
  · intro s
    apply d.fullCylinder0.hom_ext
    · rw [← Category.assoc, show d.fullLine0 ≫ d.fullMap0 = d.totalLine0 from pushout.inl_desc _ _
      _,
        totalLine0, Category.assoc]
      erw [line0_bridge_fold]
    · rw [← Category.assoc, show d.fullEnd0 ≫ d.fullMap0 = d.totalLeft from pushout.inr_desc _ _ _,
        totalLeft, Category.assoc]
      simp only [totalLeft_fold]
  · intro s
    apply d.fullCylinder1.hom_ext
    · rw [← Category.assoc, show d.fullLine1 ≫ d.fullMap1 = d.totalLine1 from pushout.inl_desc _ _
      _,
        totalLine1, Category.assoc]
      erw [line1_bridge_fold]
    · rw [← Category.assoc, show d.fullEnd1 ≫ d.fullMap1 = d.totalRight from pushout.inr_desc _ _ _,
        totalRight_fold]
  · intro s m hm0 hm1
    apply d.total_hom_ext
    · simp only [totalLine0, Category.assoc, line0_bridge_fold]
      have hh := congrArg (fun k ↦ d.fullLine0 ≫ k) hm0
      simpa only [← Category.assoc, fullMap0, fullLine0, pushout.inl_desc] using hh
    · simp only [totalLine1, Category.assoc, line1_bridge_fold]
      have hh := congrArg (fun k ↦ d.fullLine1 ≫ k) hm1
      simpa only [← Category.assoc, fullMap1, fullLine1, pushout.inl_desc] using hh
    · simp only [totalLeft, Category.assoc, totalLeft_fold]
      have hh := congrArg (fun k ↦ d.fullEnd0 ≫ k) hm0
      simpa only [← Category.assoc, fullMap0, fullEnd0, pushout.inr_desc] using hh
    · rw [totalRight_fold]
      have hh := congrArg (fun k ↦ d.fullEnd1 ≫ k) hm1
      simpa only [← Category.assoc, fullMap1, fullEnd1, pushout.inr_desc] using hh

end TopCat.FibrationSpan.Data
