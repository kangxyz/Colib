/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.Homotopy

/-! # Reversal, concatenation and based conjugation of coherent prespectrum homotopies

The original track coordinate is reversed or divided into the actual interval halves.
The structure coordinate remains independent throughout.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/HomotopyLoop.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original continuous families, independent
parameters, fixed boundaries and strict structure compatibility are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}}

/-- Reverse the actual homotopy time, preserving the original structure coordinate. -/
def Homotopy.symm {f g : E ⟶ F} (H : Homotopy f g) : Homotopy g f where
  level n := (H.levelHomotopy n).symm.toContinuousMap
  at_zero n x := (H.levelHomotopy n).symm.apply_zero x
  at_one n x := (H.levelHomotopy n).symm.apply_one x
  at_point n s := H.at_point n (unitInterval.symm s)
  comm n s x t := H.comm n (unitInterval.symm s) x t

/-- Concatenate whole structure-compatible homotopies using the actual interval halves. -/
def Homotopy.trans {f g h : E ⟶ F} (H : Homotopy f g) (K : Homotopy g h) : Homotopy f h where
  level n := ((H.levelHomotopy n).trans (K.levelHomotopy n)).toContinuousMap
  at_zero n x := ((H.levelHomotopy n).trans (K.levelHomotopy n)).apply_zero x
  at_one n x := ((H.levelHomotopy n).trans (K.levelHomotopy n)).apply_one x
  at_point n s := by
    change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (s,E.point n) = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact H.at_point _ _
    · exact K.at_point _ _
  comm n s x t := by
    change ((H.levelHomotopy (n+1)).trans (K.levelHomotopy (n+1))) (s,E.structureMap n x t) =
      F.structureMap n (((H.levelHomotopy n).trans (K.levelHomotopy n)) (s,x)) t
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact H.comm _ _ _ _
    · exact K.comm _ _ _ _

/-- Conjugate a genuine self-homotopy by the supplied original nullhomotopy. -/
def Homotopy.conjugateToZero {f : E ⟶ F} (H : Homotopy f f)
    (N : Homotopy f (zeroHom E F)) : Homotopy (zeroHom E F) (zeroHom E F) :=
  N.symm.trans (H.trans N)

end Topology.LoopPrespectrum
