/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.WeakGridBasedHomotopy
public import Colib.KTheory.Waldhausen.Additivity.RealizationHomotopy
public import Colib.Topology.Realization.EdgePath


/-! # The actual zero vertex and based forward map of ordinary outer subdivision

Only the forward endpoint is required to preserve the displayed zero vertex.
No homotopy-group isomorphism or realization-equivalence conclusion is included here.


Implementation provenance: `Quillen/Waldhausen/Additivity/SubdivisionBasepoint.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u v

namespace CategoryTheory.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- The original constant-zero grid in degrees (delta[0], [0]). -/
def subdivisionZeroVertex :
    (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)) _⦋0⦌ :=
  zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (SSet.OrdinalSubdivision.δ.obj ⦋0⦌)) (op ⦋0⦌)

/-- Its actual realization point, with no choice of path. -/
def subdivisionBasepoint :
    |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)| :=
  SSet.realizationPoint (subdivisionZeroVertex V)

/-- The original first-half endpoint takes the stated zero grid to the original zero grid. -/
@[simp]
theorem horizontalEndpoint_zeroVertex :
    (SSet.diagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))).app
      (op ⦋0⦌) (subdivisionZeroVertex V) = diagonalZeroVertex V := rfl

/-- The prescribed actual endpoint map preserves the displayed realization points. -/
@[simp]
theorem horizontalEndpoint_basepoint :
    realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))
      (subdivisionBasepoint V) = SSet.realizationPoint (diagonalZeroVertex V) := by
  rw [subdivisionBasepoint]
  exact SSet.realizationPoint_naturality _ _

end CategoryTheory.Waldhausen.Additivity
