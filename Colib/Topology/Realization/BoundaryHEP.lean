/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.SimplexBoundaryHEP
public import Colib.Topology.Realization.Boundary

/-! # Homotopy extension for the actual realized simplex boundary

Selected from `Quillen/Topology/HELP/CompactRealizationLifting.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The known finite-simplex homeomorphism
and boundary comparison transport the explicit geometric HEP to the actual map.
No compact HELP or mapping-path theorem is imported.
-/
@[expose] public noncomputable section
open CategoryTheory Convexity.StdSimplex
open scoped Simplicial Topology
universe u
namespace SSet

/-- The actual realized simplex boundary inclusion has HEP, including the
empty boundary in dimension zero. -/
theorem homotopyExtensionProperty_realizationBoundary (n : ℕ) :
    TopCat.HomotopyExtensionProperty (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u}))) := by
  let P := |(Δ[0] : SSet.{u})|
  let a := (realizationBoundaryHomeomorph n).trans
    (Homeomorph.uniqueProd P (simplexBoundary n)).symm
  let b := (FiniteSimplexAdapter.toTopHomeomorph ⦋n⦌).trans
    (Homeomorph.uniqueProd P (Convexity.StdSimplex ℝ (Fin (n + 1)))).symm
  apply TopCat.homotopyExtensionProperty_of_iso_square _
    (TopCat.parameterizedSimplexBoundaryInclusion P n) (TopCat.isoOfHomeo a) (TopCat.isoOfHomeo b)
    _ (TopCat.homotopyExtensionProperty_simplexBoundary P n)
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

end SSet
