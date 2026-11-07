/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.Basic
public import Colib.Topology.HomotopyPullback.WeakLiftingComparison

/-!
# Fiberwise deformation on an actual topological pushout

Pushing out a strong deformation which preserves a specified base map gives
an actual strong deformation over that base. In particular attaching such
a collar to a fibration gives weak covering-homotopy lifting. This uses the
cylinder's preservation of pushouts, never arbitrary pullback preservation.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/DeformationRetract/FiberwisePushout.lean` at
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

namespace TopCat.CylinderStrongDeformationRetract
variable {A B C D T : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C}
  {g : B ⟶ D} {j : C ⟶ D}
  (h : TopCat.CylinderStrongDeformationRetract i) (sq : IsPushout i f g j)

@[reassoc (attr := simp)] theorem pushout_inl_retraction :
    g ≫ (h.pushout sq).r = h.r ≫ f := by
  exact sq.inl_desc _ _ _

@[reassoc (attr := simp)] theorem pushout_inl_homotopy :
    (g ▷ TopCat.I) ≫ (h.pushout sq).H = h.H ≫ g := by
  exact (sq.map (tensorRight TopCat.I)).inl_desc _ _ _

variable (p : D ⟶ T)
  (hH : h.H ≫ g ≫ p = fst B TopCat.I ≫ g ≫ p)

include hH in
/-- The entire pushed-out deformation preserves its actual base projection. -/
theorem pushout_homotopy_over :
    (h.pushout sq).H ≫ p = fst D TopCat.I ≫ p := by
  apply (sq.map (tensorRight TopCat.I)).hom_ext
  · change (g ▷ TopCat.I) ≫ (h.pushout sq).H ≫ p =
      (g ▷ TopCat.I) ≫ fst D TopCat.I ≫ p
    rw [← Category.assoc, pushout_inl_homotopy, Category.assoc, hH]
    simp only [← Category.assoc, whiskerRight_fst]
  · change (j ▷ TopCat.I) ≫ (h.pushout sq).H ≫ p =
      (j ▷ TopCat.I) ≫ fst D TopCat.I ≫ p
    rw [← Category.assoc, (h.pushout sq).fixed,
      ← Category.assoc, whiskerRight_fst, Category.assoc]

include hH in
/-- The pushed-out retraction is strictly over the base. -/
theorem pushout_retraction_over : (h.pushout sq).r ≫ j ≫ p = p := by
  have hh := congrArg (fun k : D ⊗ TopCat.I ⟶ T ↦ TopCat.ι₀ ≫ k)
    (h.pushout_homotopy_over sq p hH)
  simpa only [← Category.assoc, (h.pushout sq).H₀, TopCat.ι₀_fst,
    Category.id_comp] using hh

include sq hH in
/-- Actual weak lifting passes from the unchanged side to the glued space
when the attached side strongly deforms to the gluing locus over the base. -/
theorem pushout_weakLifting (hp : WeakHomotopyLiftingProperty (j ≫ p).hom) :
    WeakHomotopyLiftingProperty p.hom := by
  let R := h.pushout sq
  refine weakLifting_of_fiberwise_deformation p.hom (j ≫ p).hom hp
    j.hom R.r.hom rfl ?_ (TopCat.homotopyOfCylinder R.H R.H₀ R.H₁).symm ?_
  · exact congrArg TopCat.Hom.hom (h.pushout_retraction_over sq p hH)
  · intro t d
    exact ConcreteCategory.congr_hom (h.pushout_homotopy_over sq p hH)
      (d, ULift.up (σ t))

include hH in
/-- Gluing a fiberwise strong deformation collar to a genuine fibration
gives the explicit homotopy equivalence for every strict pullback square. -/
-- Preserve the public strict-pullback comparison name used by existing downstream code.
def pushoutStrictPullbackHomotopyEquiv
    (hp : HomotopyLiftingProperty (j ≫ p).hom) {S : Type u} [TopologicalSpace S]
    (a : C(S, T)) :
    ContinuousMap.HomotopyEquiv {z : S × D // p z.2 = a z.1}
      (HomotopyPullback p.hom a) :=
  HomotopyPullback.strictPullbackHomotopyEquivOfWeakLifting p.hom a
    (h.pushout_weakLifting sq p hH hp.weak)

@[simp] theorem pushoutStrictPullbackHomotopyEquiv_toFun
    (hp : HomotopyLiftingProperty (j ≫ p).hom) {S : Type u} [TopologicalSpace S]
    (a : C(S, T)) :
    (h.pushoutStrictPullbackHomotopyEquiv sq p hH hp a).toFun =
      HomotopyPullback.strictPullbackInclusion p.hom a := rfl

end TopCat.CylinderStrongDeformationRetract
