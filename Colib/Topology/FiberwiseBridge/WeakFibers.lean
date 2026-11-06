/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseBridge.BaseChange
public import Colib.Topology.FiberwiseMappingPath.InjectiveBaseLifting
public import Colib.Topology.MappingCylinder.Compact.WeakComparison

/-!
# Weak original strict fibers supply the actual bridge-end base changes

The single-cylinder finite vertical HELP theorem supplies the weak source
map after every ambient base change. An injective base inclusion reflects
full vertical paths, so no lifting hypothesis on the ambient base is needed.
Source-collar locality and the actual target cylinder SDR then give the
original bridge target inclusion, retaining every new parameter coordinate.


Implementation provenance:
`Quillen/Topology/FiberwiseBridge/WeakFibers.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.FiberwiseMappingPath


noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.FiberwiseBridge.SourceCharts
open FiberwiseMappingPath
variable {A B C M N Z T S : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {lM : A ⊗ TopCat.I ⟶ M} {cM : B ⟶ M}
  {lN : A ⊗ TopCat.I ⟶ N} {cN : C ⟶ N}
  (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f lM cM)
  (sqN : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g lN cN)
  {m : M ⟶ Z} {n : N ⟶ Z}
  (sq : IsPushout (TopCat.ι₀ ≫ lM) (TopCat.ι₀ ≫ lN) m n)
  (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c)
  (j : T ⟶ S) (hj : Function.Injective j)

include hj in
/-- Only the other original attaching map needs weak strict fibers.
Both local collar deformations and the first target SDR are unconditional. -/
theorem leftTarget_baseChange_isWeak_of_weak_fibers
    (hp : HomotopyLiftingProperty (g ≫ c).hom)
    (hq : HomotopyLiftingProperty c.hom)
    (hN : CompactHomotopyLiftingProperty (TopCat.MappingCylinder.Compact.projection sqN c).hom)
    (hf : ∀ t : T, IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (g ≫ c).hom c.hom g.hom rfl t))
    {D : Type u} [TopologicalSpace D] (a : C(D,S)) :
    IsWeakHomotopyEquivalence (baseChangedMap
      (TopCat.FiberwiseBridge.projection sqM sqN sq b c w ≫ j).hom (cM ≫ m).hom a) := by
  have hlift := endpoint_boundaryLifting_of_injective_base
    (TopCat.MappingCylinder.Compact.projection sqN c).hom (TopCat.ι₀ ≫ lN).hom j.hom hj
    (TopCat.MappingCylinder.Compact.source_endpoint_boundaryLifting_of_weak_fibers
      sqN c hp hq hN hf)
  have hs := baseChangedMap_isWeakHomotopyEquivalence
    (j.hom.comp (TopCat.MappingCylinder.Compact.projection sqN c).hom) (TopCat.ι₀ ≫ lN).hom a hlift
  have hm : IsWeakHomotopyEquivalence (baseChangedMap
      (TopCat.FiberwiseBridge.projection sqM sqN sq b c w ≫ j).hom m.hom a) := by
    refine left_baseChange_isWeak_of_source_collars sqM sqN sq 1 zero_lt_one
      (TopCat.FiberwiseBridge.projection sqM sqN sq b c w ≫ j) ?_ ?_ a ?_
    · simpa only [Category.assoc, TopCat.FiberwiseBridge.projection_left_assoc] using
        TopCat.MappingCylinder.SourceCollar.deformation_over sqM 1 zero_lt_one (b ≫ j)
    · simpa only [Category.assoc, TopCat.FiberwiseBridge.projection_right_assoc] using
        TopCat.MappingCylinder.SourceCollar.deformation_over sqN 1 zero_lt_one (c ≫ j)
    · rw [TopCat.FiberwiseBridge.projection_right_assoc sqM sqN sq b c w j]
      exact hs
  apply baseChangedMap_comp_isWeak
    (TopCat.FiberwiseBridge.projection sqM sqN sq b c w ≫ j).hom m.hom cM.hom a hm
  exact isWeakHomotopyEquivalence_of_homotopyEquiv
    ((TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract
      sqM).baseChangeHomotopyEquiv
      (m ≫ TopCat.FiberwiseBridge.projection sqM sqN sq b c w ≫ j) (by
        simpa only [Category.assoc, TopCat.FiberwiseBridge.projection_left_assoc] using
          TopCat.MappingCylinder.mappingCylinderTargetDeformation_over sqM (b ≫ j)) a)

end TopCat.FiberwiseBridge.SourceCharts
