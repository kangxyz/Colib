/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.Basic

/-!
# Realization of constant simplicial maps

The literal constant simplicial map realizes to the constant continuous map at its realized
vertex.

## Implementation provenance

Adapted from `Quillen/Topology/Realization/Constant.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The selected declarations retain the source
constructions and mathematical universe parameters. Namespace and dependency ownership
are changed to the underlying Mathlib objects.
-/
@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- A constant simplicial map realizes to the corresponding constant continuous map. -/
theorem realization_const_apply {X Y : SSet.{u}} (y : Y _⦋0⦌) (x : |X|) :
    SSet.toTop.map (SSet.const y : X ⟶ Y) x = realizationPoint y := by
  have hv : (SSet.yonedaEquiv.symm y).app _
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u}) _⦋0⦌) = y := by
    exact SSet.yonedaEquiv.apply_symm_apply y
  have hc : (SSet.const y : X ⟶ Y) =
      SSet.const (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u}) _⦋0⦌) ≫
        SSet.yonedaEquiv.symm y := by
    rw [SSet.const_comp, hv]
  rw [hc, Functor.map_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm y) _ = _
  exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm y))
    (Subsingleton.elim _ default)

end SSet

attribute [colib_tag "COL-0061",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(1)-(2) and Definition 3.1.4" "background"
    "Functorial realization and the point simplex; this constant-map API lemma is derived here"]
  SSet.realization_const_apply
