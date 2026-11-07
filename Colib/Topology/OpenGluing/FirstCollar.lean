/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.Basic

/-!
# An actual endpoint collar in the first normalized attachment

A height on the bridge which is one on its left endpoint extends over the
unchanged first pushout. Its open upper collar is exactly the pushout of the
bridge collar and the old left end. Consequently a genuine fiberwise local
collar deformation extends over this open neighborhood. No deformation of
the whole bridge, injectivity of an attaching map, or pullback preservation
is assumed.


Implementation provenance:
`Quillen/Topology/OpenGluing/FirstCollar.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology

noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.OpenGluing.Data
variable {T : TopCat.{u}} {U V : Set T} (d : OpenGluing.Data T U V)
  (h : C(d.M, I)) (hi : ∀ a, h (d.i0 a) = 1)

/-- The bridge height extended by one on the unchanged end. -/
def firstCollarHeight : d.First ⟶ TopCat.I := pushout.desc
  (TopCat.ofHom ⟨fun m ↦ ULift.up (h m), by fun_prop⟩)
  (TopCat.ofHom ⟨fun _ ↦ ULift.up 1, continuous_const⟩) (by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.up (hi a))

@[simp] theorem firstCollarHeight_bridge (m : d.M) :
    (d.firstCollarHeight h hi (d.firstBridge m)).down = h m :=
  congrArg ULift.down (ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) m)

@[simp] theorem firstCollarHeight_end (e : d.E0) :
    (d.firstCollarHeight h hi (d.firstEnd e)).down = 1 :=
  congrArg ULift.down (ConcreteCategory.congr_hom (pushout.inr_desc _ _ _) e)

variable (cut : I)

/-- The open bridge neighborhood of the left attaching end. -/
def bridgeEndCollarSet : Set d.M := {m | cut < h m}

/-- Its actual open extension across the first pushout. -/
def firstEndCollarSet : Set d.First :=
  {x | cut < (d.firstCollarHeight h hi x).down}

theorem bridgeEndCollar_isOpen : IsOpen (d.bridgeEndCollarSet h cut) :=
  isOpen_lt continuous_const h.continuous

theorem firstEndCollar_isOpen : IsOpen (d.firstEndCollarSet h hi cut) :=
  isOpen_lt continuous_const (continuous_uliftDown.comp (d.firstCollarHeight h hi).hom.continuous)

/-- The bridge subspace where the chosen height `h` is strictly above `cut`. -/
abbrev BridgeEndCollar : TopCat.{u} := TopCat.of (d.bridgeEndCollarSet h cut)
/-- The corresponding upper-height subspace of the first pushout, using the extension of `h` by
one on the left end. -/
abbrev FirstEndCollar : TopCat.{u} := TopCat.of (d.firstEndCollarSet h hi cut)

variable (hc : cut < 1)

/-- The original attaching end maps into the actual bridge collar. -/
def bridgeEndCollarEnd : d.Q0 ⟶ d.BridgeEndCollar h cut := TopCat.ofHom
  ⟨fun a ↦ ⟨d.i0 a, by change cut < h (d.i0 a); rw [hi]; exact hc⟩, by fun_prop⟩

/-- The actual bridge-collar map into the first-pushout collar. -/
def firstEndCollarBridge : d.BridgeEndCollar h cut ⟶ d.FirstEndCollar h hi cut :=
  TopCat.ofHom ⟨fun m ↦ ⟨d.firstBridge m.1, by
    change cut < (d.firstCollarHeight h hi (d.firstBridge m.1)).down
    rw [firstCollarHeight_bridge]
    exact m.2⟩, by fun_prop⟩

/-- The unchanged end maps into the actual first-pushout collar. -/
def firstEndCollarEnd : d.E0 ⟶ d.FirstEndCollar h hi cut := TopCat.ofHom
  ⟨fun e ↦ ⟨d.firstEnd e, by
    change cut < (d.firstCollarHeight h hi (d.firstEnd e)).down
    rw [firstCollarHeight_end]
    exact hc⟩, by fun_prop⟩

@[simp] theorem bridgeEndCollarEnd_val (a : d.Q0) :
    (d.bridgeEndCollarEnd h hi cut hc a).1 = d.i0 a := rfl
@[simp] theorem firstEndCollarBridge_val (m : d.BridgeEndCollar h cut) :
    (d.firstEndCollarBridge h hi cut m).1 = d.firstBridge m.1 := rfl
@[simp] theorem firstEndCollarEnd_val (e : d.E0) :
    (d.firstEndCollarEnd h hi cut hc e).1 = d.firstEnd e := rfl

private def allSubtypeHomeomorph {X : Type u} [TopologicalSpace X]
    (P : X → Prop) (hP : ∀ x, P x) : X ≃ₜ {x // P x} where
  toFun x := ⟨x, hP x⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_subtype_val

/-- Open restriction gives the actual collar pushout, with unchanged end
and attaching maps. Only openness of the vertex collar is used. -/
theorem firstEndCollar_isPushout :
    IsPushout (d.bridgeEndCollarEnd h hi cut hc) d.inclusion0
      (d.firstEndCollarBridge h hi cut) (d.firstEndCollarEnd h hi cut hc) := by
  let N := d.firstEndCollarSet h hi cut
  let es : d.Q0 ≃ₜ OpenPushout.source (i := d.i0) (g := d.firstBridge) N :=
    allSubtypeHomeomorph _ (fun a ↦ by
      change cut < (d.firstCollarHeight h hi (d.firstBridge (d.i0 a))).down
      rw [firstCollarHeight_bridge, hi]
      exact hc)
  let el : d.BridgeEndCollar h cut ≃ₜ OpenPushout.left (g := d.firstBridge) N :=
    Homeomorph.setCongr (by
      ext m
      change (cut < h m) ↔ cut < (d.firstCollarHeight h hi (d.firstBridge m)).down
      rw [firstCollarHeight_bridge])
  let er : d.E0 ≃ₜ OpenPushout.right (j := d.firstEnd) N :=
    allSubtypeHomeomorph _ (fun e ↦ by
      change cut < (d.firstCollarHeight h hi (d.firstEnd e)).down
      rw [firstCollarHeight_end]
      exact hc)
  exact (OpenPushout.isPushout d.first_isPushout N (d.firstEndCollar_isOpen h hi cut)).of_iso'
    (TopCat.isoOfHomeo es) (TopCat.isoOfHomeo el) (TopCat.isoOfHomeo er) (Iso.refl _)
    (by ext a; rfl) (by ext a; rfl) (by ext m; rfl) (by ext e; rfl)

/-- Actual base projections on the two collars. -/
def bridgeEndCollarBase : d.BridgeEndCollar h cut ⟶ T :=
  TopCat.ofHom ⟨fun m ↦ d.bridgeBase m.1, by fun_prop⟩
/-- The ambient base map `firstBase` restricted to the first attachment endpoint collar, with
codomain `T`. -/
def firstEndCollarBase : d.FirstEndCollar h hi cut ⟶ T :=
  TopCat.ofHom ⟨fun x ↦ d.firstBase x.1, by fun_prop⟩
/-- The left-chart projection `firstProjection` restricted to the first attachment endpoint
collar, with codomain `U`. -/
def firstEndCollarProjection : d.FirstEndCollar h hi cut ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x ↦ d.firstProjection x.1, by fun_prop⟩

@[reassoc (attr := simp)] theorem firstEndCollarBridge_base :
    d.firstEndCollarBridge h hi cut ≫ d.firstEndCollarBase h hi cut =
      d.bridgeEndCollarBase h cut := by
  ext m
  exact d.firstBridge_base_apply m.1

@[reassoc (attr := simp)] theorem firstEndCollarEnd_projection :
    d.firstEndCollarEnd h hi cut hc ≫ d.firstEndCollarProjection h hi cut = d.p0 := by
  apply ConcreteCategory.hom_ext
  intro e
  exact ConcreteCategory.congr_hom d.firstEnd_projection e

/-- A genuine local bridge deformation yields a genuine local deformation
of the original end in the unchanged first attachment. -/
def firstEndCollarStrongDeformationRetract
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc)) :
    TopCat.CylinderStrongDeformationRetract (d.firstEndCollarEnd h hi cut hc) :=
  R.pushout (d.firstEndCollar_isPushout h hi cut hc)

/-- The entire pushed-out deformation retains the original base point. -/
theorem firstEndCollarStrongDeformationRetract_over
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc))
    (hR : R.H ≫ d.bridgeEndCollarBase h cut =
      fst (d.BridgeEndCollar h cut) TopCat.I ≫ d.bridgeEndCollarBase h cut) :
    (d.firstEndCollarStrongDeformationRetract h hi cut hc R).H ≫
        d.firstEndCollarBase h hi cut =
      fst (d.FirstEndCollar h hi cut) TopCat.I ≫ d.firstEndCollarBase h hi cut := by
  apply R.pushout_homotopy_over (d.firstEndCollar_isPushout h hi cut hc)
  simpa only [firstEndCollarBridge_base] using hR

include hc in
/-- Every point outside the overlap base already lies in the unchanged
end. This is the geometric reason whole vertical tracks there stay inside
the open endpoint collar. -/
theorem firstEndCollar_contains_complement (x : d.First) (hx : d.firstBase x ∉ V) :
    x ∈ d.firstEndCollarSet h hi cut := by
  rcases Types.eq_or_eq_of_isPushout (d.first_isPushout.map (forget TopCat)) x with
    ⟨m, hm⟩ | ⟨e, he⟩
  · change d.firstBridge m = x at hm
    have hmV : d.firstBase (d.firstBridge m) ∈ V := by
      rw [firstBridge_base_apply]
      exact (d.q m).2.2
    exact False.elim (hx (hm ▸ hmV))
  · change d.firstEnd e = x at he
    rw [← he]
    exact (d.firstEndCollarEnd h hi cut hc e).2

include hc in
/-- The endpoint collar and the genuine bridge base-chart cover the first
attachment, including empty overlap cases. -/
theorem firstEndCollar_cover :
    d.firstEndCollarSet h hi cut ∪ d.firstBase ⁻¹' V = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
  by_cases hx : d.firstBase x ∈ V
  · exact Or.inr hx
  · exact Or.inl (d.firstEndCollar_contains_complement h hi cut hc x hx)

end TopCat.OpenGluing.Data
