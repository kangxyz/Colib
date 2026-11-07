/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingCylinder.Compact.BoundaryLifting
public import Colib.Topology.HELP.WeakFiberCube

/-!
# Weak-fiber comparison for the compact mapping cylinder

Weak equivalences on the specified fibers give endpoint boundary lifting for the
    mapping-cylinder source map.


Implementation provenance:
`Quillen/Topology/MappingCylinder/Compact/WeakComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalTests



noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval Simplicial
universe u
namespace TopCat.MappingCylinder.Compact
open CubicalTests
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)

/-- Full vertical HELP for the original source end, only on actual finite
cubes, with complete empty-aware weak input on the original strict fibers. -/
theorem source_cube_fullHELP_of_weak_fibers
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (hM : CompactHomotopyLiftingProperty (projection sq base).hom)
    (hf : ∀ t : T,IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t))
    (n : ℕ) (a : C(boundary.{u} n,A)) (b : C(cube.{u} n,M))
    (H : (((TopCat.ι₀ ≫ l).hom).comp a).Homotopy (b.comp (boundaryInclusion n).hom))
    (hH : ∀ t x,projection sq base (H (t,x)) = projection sq base (b x.val)) :
    ∃ a' : C(cube.{u} n,A),a'.comp (boundaryInclusion n).hom = a ∧
      (f ≫ base).hom.comp a' = (projection sq base).hom.comp b ∧
      ∃ V : (((TopCat.ι₀ ≫ l).hom).comp a').Homotopy b,
        HomotopyOver ((projection sq base).hom.comp b) (projection sq base).hom V ∧
          ∀ (t : unitInterval) (x : boundary.{u} n),V (t,x.val) = H (t,x) := by
  let : CompactSpace (boundaryPresentation.{u} n).space := (boundaryPresentation n).compact
  let : CompactSpace (boundary.{u} n) := (boundaryPresentationHomeomorph n).compactSpace
  let i := boundaryInclusion.{u} n
  have hzero : ∀ x,boundaryDuration n x = 0 ↔ x ∈ Set.range i := by
    intro x
    rw [boundaryDuration_eq_zero_iff]
    exact ⟨fun hx ↦ ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ ↦ hy ▸ y.property⟩
  let r : C(M,C) := (TopCat.MappingCylinder.mappingCylinderProjection sq).hom
  let j : C(A,M) := (TopCat.ι₀ ≫ l).hom
  have hrj : r.comp j = f.hom := congrArg TopCat.Hom.hom
    (TopCat.MappingCylinder.mappingCylinderProjection_start sq)
  let Hf : (f.hom.comp a).Homotopy ((r.comp b).comp i.hom) :=
    ((ContinuousMap.Homotopy.refl r).comp H).cast (by rw [← hrj]; rfl) rfl
  obtain ⟨a',ha',hbase,J,hJ,hJa⟩ := weak_fullHELP_on_cube_over_base
    (f ≫ base).hom base.hom f.hom rfl hp hq hf n a (r.comp b) Hf hH
  let H' : ((j.comp a').comp i.hom).Homotopy (b.comp i.hom) :=
    H.cast (by rw [ContinuousMap.comp_assoc,ha']) rfl
  let J' : (r.comp (j.comp a')).Homotopy (r.comp b) :=
    J.cast (by rw [← ContinuousMap.comp_assoc,hrj]) rfl
  have hr : CompactHomotopyExtensionLiftingProperty r := compactHELP_of_homotopyEquiv
    (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).toHomotopyEquiv.symm
  obtain ⟨V,hV,hVa⟩ := compact_vertical_homotopy_lift
    (projection sq base).hom base.hom r rfl hM hq.compact hr _ _ i (boundaryInclusion_hep n)
    (boundaryDuration n) hzero (j.comp a') b H' J' hJ hJa
  exact ⟨a',ha',hbase,V,hV,hVa⟩

/-- Exact original vertical endpoint lifting from actual weak fiber maps,
including every stored boundary path and dimension zero. -/
theorem source_endpoint_boundaryLifting_of_weak_fibers
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (hM : CompactHomotopyLiftingProperty (projection sq base).hom)
    (hf : ∀ t : T,IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t)) :
    CubicalSubdivision.BoundaryLifting
      (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom) := by
  apply CubicalSubdivision.boundaryLifting_of_hasLiftingProperty
  intro n
  apply FiberwiseMappingPath.endpoint_hasLiftingProperty_of_pairHELP
  intro a b H hH
  obtain ⟨a',ha',_,V,hV,hA⟩ := source_cube_fullHELP_of_weak_fibers sq base hp hq hM hf n a b H hH
  exact ⟨a',ha',V,hV,hA⟩

/-- A genuine base realization model supplies the finite projection lifting
input while the attaching strict fibers need only the complete weak property. -/
theorem source_endpoint_boundaryLifting_of_weak_fibers_realizationModel
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (X : SSet.{u}) (e : T ≃ₜ |X|)
    (hf : ∀ t : T,IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t)) :
    CubicalSubdivision.BoundaryLifting
      (FiberwiseMappingPath.endpoint (projection sq base).hom (TopCat.ι₀ ≫ l).hom) :=
  source_endpoint_boundaryLifting_of_weak_fibers sq base hp hq
    (compactHomotopyLiftingProperty_of_realizationModel sq base hp hq X e) hf

end TopCat.MappingCylinder.Compact

end
