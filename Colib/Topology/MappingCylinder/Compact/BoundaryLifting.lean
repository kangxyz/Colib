/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingCylinder.Compact.CompactHELP
public import Colib.Topology.FiberwiseMappingPath.BoundaryLifting

/-!
# Endpoint boundary lifting for the mapping cylinder

Compact vertical HELP supplies endpoint boundary lifts for the source map with the prescribed
    base and endpoint data.


Implementation provenance:
`Quillen/Topology/MappingCylinder/Compact/BoundaryLifting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval Simplicial
universe u
namespace TopCat.MappingCylinder.Compact
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)

/-- The literal source inclusion's vertical endpoint has full finite
cube-boundary RLP, derived from the original attaching-map fiber HELP. -/
theorem source_endpoint_boundaryLifting
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (hM : CompactHomotopyLiftingProperty (projection sq base).hom)
    (hf : ∀ t : T,CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t)) :
    CubicalSubdivision.BoundaryLifting
      (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom) := by
  apply CubicalSubdivision.boundaryLifting_of_hasLiftingProperty
  intro n
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  apply FiberwiseMappingPath.endpoint_hasLiftingProperty_of_pairHELP
  intro a b H hH
  have hzero : ∀ x,CubicalTests.boundaryDuration n x = 0 ↔
      x ∈ Set.range (CubicalTests.boundaryInclusion.{u} n) := by
    intro x
    rw [CubicalTests.boundaryDuration_eq_zero_iff]
    exact ⟨fun hx ↦ ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ ↦ hy ▸ y.property⟩
  obtain ⟨a',ha',_,V,hV,hA⟩ := source_fullHELP_over_contracted_test
    sq base hp hq hM hf _ _ (CubicalTests.boundaryInclusion n)
    (CubicalTests.boundaryInclusion_hep n) (CubicalTests.zero n) (CubicalTests.contraction n)
    (CubicalTests.boundaryDuration n) hzero a b H hH
  exact ⟨a',ha',V,hV,hA⟩

/-- The actual realization model supplies the finite cylinder lifting
property used by the exact original endpoint theorem. -/
theorem source_endpoint_boundaryLifting_of_realizationModel
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (X : SSet.{u}) (e : T ≃ₜ |X|)
    (hf : ∀ t : T,CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t)) :
    CubicalSubdivision.BoundaryLifting
      (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom) :=
  source_endpoint_boundaryLifting sq base hp hq
    (compactHomotopyLiftingProperty_of_realizationModel sq base hp hq X e) hf

end TopCat.MappingCylinder.Compact

end
