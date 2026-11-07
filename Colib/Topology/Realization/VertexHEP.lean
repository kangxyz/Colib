/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.MonomorphismHEP
public import Colib.Topology.Realization.Basic
public import Colib.Topology.Homotopy.ExtensionContinuous

/-!
# Homotopy extension at actual realized vertices

The inclusion of the literal point represented by a simplicial vertex has the homotopy extension
property. The proof uses the actual monomorphism from the standard zero-simplex and its realized
HEP, with no change of basepoint or homotopy-equivalent replacement of the realization.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/VertexHEP.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original objects, maps,
point hypotheses, whole stored cylinder paths and universe parameters are
retained. Native namespace and lower-import ownership are used. -/
@[expose] public section
noncomputable section

open CategoryTheory
open scoped Simplicial Topology unitInterval
universe u
namespace SSet

/-- A chosen vertex defines an actual simplicial monomorphism from the zero-simplex. -/
theorem mono_vertex {X : SSet.{u}} (x : X _⦋0⦌) : Mono (SSet.yonedaEquiv.symm x) :=
  SSet.stdSimplex.isTerminalObj₀.mono_from _

/-- The literal realized vertex is a well-based point: its singleton inclusion has HEP. -/
theorem homotopyExtensionProperty_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (realizationPoint x))) := by
  let : Mono (SSet.yonedaEquiv.symm x) := mono_vertex x
  have hi := homotopyExtensionProperty_realization_mono (SSet.yonedaEquiv.symm x)
  apply TopCat.homotopyExtensionProperty_of_continuous
  intro Z f H hzero
  let H' : C(unitInterval × |(Δ[0] : SSet.{u})|, Z) :=
    ⟨fun z ↦ H (z.1, PUnit.unit), by fun_prop⟩
  have hv (a : |(Δ[0] : SSet.{u})|) :
      SSet.toTop.map (SSet.yonedaEquiv.symm x) a = realizationPoint x := by
    exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm x)) (Subsingleton.elim a default)
  obtain ⟨K, hKzero, hK⟩ := TopCat.homotopyExtensionProperty_continuous hi Z f H' (by
    intro a
    change H (0, PUnit.unit) = f (SSet.toTop.map (SSet.yonedaEquiv.symm x) a)
    rw [hv]
    exact hzero PUnit.unit)
  refine ⟨K, hKzero, ?_⟩
  intro t a
  cases a
  exact hK t default

end SSet
