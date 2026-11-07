/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseBridge.SourceCharts
public import Colib.Topology.FiberwiseMappingPath.BaseChangeComposition
public import Colib.Topology.DeformationRetract.FiberwiseBaseChange
public import Colib.Topology.FiberwiseMappingPath.BaseChangeCharts

/-!
# Actual weak bridge inclusions after arbitrary base change

The two source-collar charts and their overlap are pulled back as literal
subspaces. Genuine fiberwise collar deformations handle two restrictions;
commutative-square cancellation handles the third using the original weak
source inclusion in the other mapping cylinder. Ordinary finite-intersection
weak locality then proves the original bridge inclusion weak. No pullback of
a pushout, arbitrary weak-equivalence base-change, or global bridge SDR is used.


Implementation provenance:
`Quillen/Topology/FiberwiseBridge/BaseChange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalSubdivision
open Topology.FiberwiseMappingPath


noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.FiberwiseBridge.SourceCharts
open FiberwiseMappingPath CubicalSubdivision
variable {A B C M N Z T : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {lM : A ⊗ TopCat.I ⟶ M} {cM : B ⟶ M}
  {lN : A ⊗ TopCat.I ⟶ N} {cN : C ⟶ N}
  (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f lM cM)
  (sqN : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g lN cN)
  {m : M ⟶ Z} {n : N ⟶ Z}
  (sq : IsPushout (TopCat.ι₀ ≫ lM) (TopCat.ι₀ ≫ lN) m n)
  (cut : I) (hcut : 0 < cut) (p : Z ⟶ T)
  (hM : (TopCat.MappingCylinder.SourceCollar.strongDeformationRetract sqM cut hcut).H ≫
    TopCat.MappingCylinder.SourceCollar.inclusion sqM cut ≫ m ≫ p =
    fst (TopCat.MappingCylinder.SourceCollar.Collar sqM cut) TopCat.I ≫
      TopCat.MappingCylinder.SourceCollar.inclusion sqM cut ≫ m ≫ p)
  (hN : (TopCat.MappingCylinder.SourceCollar.strongDeformationRetract sqN cut hcut).H ≫
    TopCat.MappingCylinder.SourceCollar.inclusion sqN cut ≫ n ≫ p =
    fst (TopCat.MappingCylinder.SourceCollar.Collar sqN cut) TopCat.I ≫
      TopCat.MappingCylinder.SourceCollar.inclusion sqN cut ≫ n ≫ p)
  {D : Type u} [TopologicalSpace D] (a : C(D, T))

include hM in
/-- In the chart containing the whole right cylinder, the pulled-back collar
map is weak by the actual square and the genuine source-collar deformations. -/
theorem sideCollar_baseChange_isWeak
    (hstart : IsWeakHomotopyEquivalence (baseChangedMap (n ≫ p).hom (TopCat.ι₀ ≫ lN).hom a)) :
    IsWeakHomotopyEquivalence (baseChangedMap (sideInclusion sqM sq cut ≫ p).hom
      (sideCollar sqM sq cut).hom a) := by
  apply baseChangedMap_isWeak_of_square (sideInclusion sqM sq cut ≫ p).hom
    (TopCat.MappingCylinder.SourceCollar.source sqM cut hcut).hom (TopCat.ι₀ ≫ lN).hom
    (sideCollar sqM sq cut).hom (sideEnd sqM sq cut hcut).hom
    (congrArg TopCat.Hom.hom (side_isPushout sqM sq cut hcut).w) a
  · exact isWeakHomotopyEquivalence_of_homotopyEquiv
      ((TopCat.MappingCylinder.SourceCollar.strongDeformationRetract sqM cut
        hcut).baseChangeHomotopyEquiv
        (TopCat.MappingCylinder.SourceCollar.inclusion sqM cut ≫ m ≫ p) hM a)
  · exact hstart
  · exact isWeakHomotopyEquivalence_of_homotopyEquiv
      ((sideStrongDeformationRetract sqM sq cut hcut).baseChangeHomotopyEquiv
        (sideInclusion sqM sq cut ≫ p)
        (sideStrongDeformationRetract_over sqM sq cut hcut p hM) a)

include sq hM hN in
/-- Weakness of the original bridge leg follows after this base change from
weakness of the other original cylinder source leg after the same base change. -/
theorem left_baseChange_isWeak_of_source_collars
    (hstart : IsWeakHomotopyEquivalence (baseChangedMap (n ≫ p).hom (TopCat.ι₀ ≫ lN).hom a)) :
    IsWeakHomotopyEquivalence (baseChangedMap p.hom m.hom a) := by
  apply isWeakHomotopyEquivalence_of_two_open (baseChangedMap p.hom m.hom a)
    {z : BaseChangedTarget p.hom a | z.val.2 ∈ sideSet sqM sq cut}
    {z : BaseChangedTarget p.hom a | z.val.2 ∈ sideSet sqN sq.flip cut}
  · exact (side_isOpen sqM sq cut).preimage (by fun_prop)
  · exact (side_isOpen sqN sq.flip cut).preimage (by fun_prop)
  · change (fun z : BaseChangedTarget p.hom a ↦ z.val.2) ⁻¹'
      (sideSet sqM sq cut ∪ sideSet sqN sq.flip cut) = Set.univ
    rw [side_cover sqM sq cut hcut sqN]
    rfl
  · apply baseChangedRestriction_isWeak_of_chart p.hom m.hom a (sideSet sqM sq cut)
      (sideCollar sqM sq cut).hom (sideInclusion sqM sq cut ≫ p).hom
      (sideSourceHomeomorph sqM sq cut) (Homeomorph.refl _) (fun _ ↦ rfl) (fun _ ↦ rfl)
    exact sideCollar_baseChange_isWeak sqM sq cut hcut p hM a hstart
  · apply baseChangedRestriction_isWeak_of_chart p.hom m.hom a (sideSet sqN sq.flip cut)
      (sideEnd sqN sq.flip cut hcut).hom (sideInclusion sqN sq.flip cut ≫ p).hom
      (sideEndSourceHomeomorph sqN sq.flip cut hcut) (Homeomorph.refl _)
      (fun _ ↦ rfl) (fun _ ↦ rfl)
    exact isWeakHomotopyEquivalence_of_homotopyEquiv
      ((sideStrongDeformationRetract sqN sq.flip cut hcut).baseChangeHomotopyEquiv
        (sideInclusion sqN sq.flip cut ≫ p)
        (sideStrongDeformationRetract_over sqN sq.flip cut hcut p hN) a)
  · apply baseChangedRestriction_isWeak_of_chart p.hom m.hom a (intersectionSet sqM sq cut sqN)
      (intersectionLeft sqM sq cut hcut sqN).hom (intersectionInclusion sqM sq cut sqN ≫ p).hom
      (intersectionSourceHomeomorph sqM sq cut hcut sqN) (Homeomorph.refl _)
      (fun _ ↦ rfl) (fun _ ↦ rfl)
    exact isWeakHomotopyEquivalence_of_homotopyEquiv
      ((intersectionStrongDeformationRetract sqM sq cut hcut sqN).baseChangeHomotopyEquiv
        (intersectionInclusion sqM sq cut sqN ≫ p)
        (intersectionStrongDeformationRetract_over sqM sq cut hcut sqN p hN) a)

omit cut hcut p hM hN in
/-- The complete local deformations are obtained from the original cylinder
base projection. The sole weak input is the actual other-cylinder source map. -/
theorem left_baseChange_isWeakHomotopyEquivalence
    (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c)
    (hstart : IsWeakHomotopyEquivalence
      (baseChangedMap (TopCat.MappingCylinder.mappingCylinderProjection sqN ≫ c).hom (TopCat.ι₀ ≫
        lN).hom a)) :
    IsWeakHomotopyEquivalence
      (baseChangedMap (TopCat.FiberwiseBridge.projection sqM sqN sq b c w).hom m.hom a) := by
  refine left_baseChange_isWeak_of_source_collars sqM sqN sq 1 (by exact zero_lt_one)
    (TopCat.FiberwiseBridge.projection sqM sqN sq b c w) ?_ ?_ a ?_
  · simpa only [TopCat.FiberwiseBridge.projection_left] using
      TopCat.MappingCylinder.SourceCollar.deformation_over sqM 1 (by exact zero_lt_one) b
  · simpa only [TopCat.FiberwiseBridge.projection_right] using
      TopCat.MappingCylinder.SourceCollar.deformation_over sqN 1 (by exact zero_lt_one) c
  · rw [TopCat.FiberwiseBridge.projection_right sqM sqN sq b c w]
    exact hstart

end TopCat.FiberwiseBridge.SourceCharts
