/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.HomotopyComposition
public import Colib.Topology.Prespectrum.ParameterLooping

/-! # Original loop maps obtained from a specified nullhomotopy

Conjugation and parameter transposition retain the actual based loop.
The source's mapping-cone transitions are not part of this cone-independent owner.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/HomotopyLoop.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original continuous families, independent
parameters, fixed boundaries and strict structure compatibility are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}}

/-- The actual loop map at the zero point, with the necessary parameter interchange explicit. -/
def Homotopy.nullLoopMap {f : E ⟶ F} (H : Homotopy f f)
    (N : Homotopy f (zeroHom E F)) : E ⟶ parameterLooping F :=
  (H.conjugateToZero N).zeroLoopMap

end Topology.LoopPrespectrum
