/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.StrictComparison
public import Colib.Topology.Pushout.HomotopyEquivalence
public import Colib.Topology.MappingCylinder.HomotopyExtension

/-! Actual pullbacks over a base collar retraction. The interval
contraction stays in each fiber of the retraction, so the end is a genuine
homotopy equivalent subspace of every such pullback. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/RetractionBaseChange.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology

/-- Actual covering-homotopy lifting is preserved by arbitrary base change. -/
theorem HomotopyLiftingProperty.baseChange
    {E B X : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
    (p : C(E, B)) (r : C(X, B)) (hp : HomotopyLiftingProperty p) :
    HomotopyLiftingProperty (HomotopyPullback.strictBaseProjection p r) := by
  intro A _ a H hzero
  let a' : C(A, E) := ⟨fun x ↦ (a x).1.2, by fun_prop⟩
  obtain ⟨L, hL0, hL⟩ := hp A a' (r.comp H) (fun x ↦ by
    change r (H (0, x)) = p (a x).1.2
    rw [hzero]
    exact (a x).2.symm)
  let L' : C(I × A, {z : X × E // p z.2 = r z.1}) :=
    ⟨fun z ↦ ⟨(H z, L z), hL z.1 z.2⟩, by fun_prop⟩
  refine ⟨L', ?_, fun _ _ ↦ rfl⟩
  intro x
  apply Subtype.ext
  exact Prod.ext (hzero x) (hL0 x)

end Topology

open Topology
namespace TopCat.RetractionPullback
variable {B X E : TopCat.{u}} {i : B ⟶ X}
  (R : TopCat.CylinderStrongDeformationRetract i) (p : E ⟶ B)

/-- The strict pullback of `p : E ⟶ B` along the collar retraction `R.r : X ⟶ B`. -/
abbrev Space := {z : X × E // p z.2 = R.r z.1}
/-- Include `E` in the strict pullback by pairing each point with its image under the endpoint
inclusion `i`. -/
def inclusion : C(E, Space R p) where
  toFun e := ⟨(i (p e), e), (ConcreteCategory.congr_hom R.retract (p e)).symm⟩
  continuous_toFun := by fun_prop

/-- The projection from the strict pullback to its `E` coordinate. -/
def retraction : C(Space R p, E) := ⟨fun z ↦ z.1.2, by fun_prop⟩

variable (hR : R.H ≫ R.r = fst X TopCat.I ≫ R.r)

/-- The homotopy from inclusion after retraction to the identity on the strict pullback,
retaining the `E` coordinate when the collar deformation preserves `R.r`. -/
def deformation : ((inclusion R p).comp (retraction R p)).Homotopy
    (ContinuousMap.id (Space R p)) where
  toFun z := ⟨(R.H (z.2.1.1, ULift.up z.1), z.2.1.2),
    z.2.2.trans (ConcreteCategory.congr_hom hR (z.2.1.1, ULift.up z.1)).symm⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (ConcreteCategory.congr_hom R.H₀ z.1.1).trans (congrArg i z.2.symm)
    · rfl
  map_one_left z := by
    apply Subtype.ext
    exact Prod.ext (ConcreteCategory.congr_hom R.H₁ z.1.1) rfl

/-- Every pullback of a retraction-invariant collar deformation has the
original end as an actual homotopy equivalent subspace. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv E (Space R p) where
  toFun := inclusion R p
  invFun := retraction R p
  left_inv := ContinuousMap.Homotopic.refl _
  right_inv := ⟨deformation R p hR⟩

@[simp] theorem homotopyEquiv_toFun : (homotopyEquiv R p hR).toFun = inclusion R p := rfl

section Comparison
variable {Y : TopCat.{u}} {j : E ⟶ Y}
  (S : TopCat.CylinderStrongDeformationRetract j) (b : Y ⟶ X)
  (w : b ≫ R.r = S.r ≫ p) (wj : j ≫ b = p ≫ i)

/-- The canonical comparison from a mapped collar into the genuine
pullback of the end over the base collar. -/
def comparison : Y ⟶ TopCat.of (Space R p) := TopCat.ofHom
  ⟨fun y ↦ ⟨(b y, S.r y), (ConcreteCategory.congr_hom w y).symm⟩, by fun_prop⟩

include wj in
theorem comparison_end : j ≫ comparison R p S b w = TopCat.ofHom (inclusion R p) := by
  apply ConcreteCategory.hom_ext
  intro e
  apply Subtype.ext
  exact Prod.ext (ConcreteCategory.congr_hom wj e) (ConcreteCategory.congr_hom S.retract e)

/-- Naturality of the two collar retractions identifies the canonical
local comparison itself as a homotopy equivalence. -/
def comparisonHomotopyEquiv : ContinuousMap.HomotopyEquiv Y (Space R p) :=
  TopCat.homotopyEquivCancelLeft (A := E) (B := Y) (C := TopCat.of (Space R p))
    (b := comparison R p S b w) S.toHomotopyEquiv rfl (homotopyEquiv R p hR)
    (congrArg TopCat.Hom.hom (comparison_end R p S b w wj).symm)

@[simp] theorem comparisonHomotopyEquiv_toFun :
    (comparisonHomotopyEquiv R p hR S b w wj).toFun = (comparison R p S b w).hom := rfl

end Comparison
end TopCat.RetractionPullback
