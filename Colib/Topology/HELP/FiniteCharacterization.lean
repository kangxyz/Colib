/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.WeakFinite
public import Colib.Topology.CubicalSubdivision.BoundaryWeakEquivalence

/-! # Weak equivalences characterized by literal finite cube HELP

Complete weakness of the original map is equivalent to full prescribed-boundary
HELP on every actual finite cube, including dimension zero. Equivalently, the
original mapping-path endpoint has literal finite cube-boundary lifting.
No CW-type hypothesis, full compact HELP or ordinary homotopy inverse is used.


Implementation provenance:
`Quillen/Topology/HELP/FiniteCharacterization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
open scoped Topology
universe u
namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Full HELP on all literal finite cube-boundary pairs, retaining the whole
original prescribed boundary homotopy. Dimension zero is included. -/
def FiniteCubeHELP (f : C(X, Y)) : Prop :=
  ∀ (n : ℕ) (a : C(CubicalTests.boundary.{u} n,X)) (b : C(CubicalTests.cube.{u} n,Y))
    (H : (f.comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion n).hom)),
    ∃ c : C(CubicalTests.cube.{u} n,X), c.comp (CubicalTests.boundaryInclusion n).hom = a ∧
      ∃ K : (f.comp c).Homotopy b,
        ∀ (t : unitInterval) (z : CubicalTests.boundary.{u} n), K (t,z.val) = H (t,z)

/-- The exact original mapping-path endpoint lifts every finite cube boundary
if and only if the original map is a complete weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_iff_mappingPath_boundaryLifting (f : C(X, Y)) :
    IsWeakHomotopyEquivalence f ↔ CubicalSubdivision.BoundaryLifting (MappingPath.endpoint f) := by
  constructor
  · exact IsWeakHomotopyEquivalence.mappingPath_endpoint_boundaryLifting
  · intro h
    have hi := isWeakHomotopyEquivalence_of_homotopyEquiv (MappingPath.inclusionHomotopyEquiv f)
    have he := h.isWeakHomotopyEquivalence.comp hi
    change IsWeakHomotopyEquivalence
      ((MappingPath.endpoint f).comp (MappingPath.inclusion f)) at he
    simpa only [MappingPath.endpoint_inclusion] using he

/-- Literal finite full HELP gives strict boundary lifting of the actual
mapping-path endpoint, without changing any stored boundary path. -/
theorem FiniteCubeHELP.mappingPath_boundaryLifting {f : C(X, Y)} (hf : FiniteCubeHELP f) :
    CubicalSubdivision.BoundaryLifting (MappingPath.endpoint f) := by
  apply CubicalSubdivision.boundaryLifting_of_hasLiftingProperty
  intro n
  exact MappingPath.endpoint_hasLiftingProperty_of_pairHELP f
    (CubicalTests.boundaryInclusion n) (hf n)

/-- The finite cube condition is an exact characterization, including empty
spaces and degree zero, rather than an arbitrary compact-pair lifting claim. -/
theorem isWeakHomotopyEquivalence_iff_finiteCubeHELP (f : C(X, Y)) :
    IsWeakHomotopyEquivalence f ↔ FiniteCubeHELP f := by
  constructor
  · intro hf
    exact hf.cube_fullHELP
  · intro hf
    exact (isWeakHomotopyEquivalence_iff_mappingPath_boundaryLifting f).mpr
      hf.mappingPath_boundaryLifting

end Topology
