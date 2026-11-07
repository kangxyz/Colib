/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.Homotopy

/-!
# Relative homotopies between coherent prespectrum homotopies

A two-parameter comparison of two specified based homotopies fixes their two original endpoints
and their basepoint line. Each level uses mathlib's actual continuous relative homotopy; the only
additional compatibility concerns the independent original prespectrum structure coordinate.
This is data for comparing supplied tracks, not an assertion that such data always exist.
-/

/-! Implementation provenance:
`Quillen/Topology/Prespectrum/RelativeHomotopy.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original continuous families, independent
parameters, fixed boundaries and strict structure compatibility are retained. -/
@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Topology.LoopPrespectrum

/-- A whole homotopy of homotopies, relative to both endpoint maps and the basepoint line. -/
structure Homotopy.RelHomotopy {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H K : Homotopy f g) where
  /-- Actual relative continuous homotopies at every level. -/
  level (n : ℕ) : (H.level n).HomotopyRel (K.level n)
    {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = E.point n}
  /-- The comparison and original homotopy times are independent of structure time. -/
  comm (n : ℕ) (r s : unitInterval) (x : E.space n) (t : unitInterval) :
    level (n + 1) (r, (s, E.structureMap n x t)) =
      F.structureMap n (level n (r, (s, x))) t

namespace Homotopy.RelHomotopy

variable {E F G : LoopPrespectrum.{u}} {f g : E ⟶ F} {H K : Homotopy f g}

/-- Every comparison-time slice is an original whole coherent based homotopy. -/
def «at» (J : H.RelHomotopy K) (r : unitInterval) : Homotopy f g where
  level n := ⟨fun z ↦ J.level n (r, z), by fun_prop⟩
  at_zero n x := ((J.level n).eq_fst r (x := (0, x)) (Or.inl rfl)).trans (H.at_zero n x)
  at_one n x := ((J.level n).eq_fst r (x := (1, x)) (Or.inr (Or.inl rfl))).trans (H.at_one n x)
  at_point n s := ((J.level n).eq_fst r (x := (s, E.point n))
    (Or.inr (Or.inr rfl))).trans (H.at_point n s)
  comm n s x t := J.comm n r s x t

/-- The initial comparison face is the first supplied homotopy. -/
@[simp]
theorem at_zero (J : H.RelHomotopy K) : J.at 0 = H := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  intro z
  exact (J.level n).apply_zero z

/-- The final comparison face is the second supplied homotopy. -/
@[simp]
theorem at_one (J : H.RelHomotopy K) : J.at 1 = K := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  intro z
  exact (J.level n).apply_one z

/-- A constant comparison preserves the entire given track. -/
def refl (H : Homotopy f g) : H.RelHomotopy H where
  level n := ContinuousMap.HomotopyRel.refl (H.level n) _
  comm n _r s x t := H.comm n s x t

/-- Postcomposition retains the actual two-parameter comparison and its fixed boundary. -/
def postcomp (J : H.RelHomotopy K) (h : F ⟶ G) :
    (H.postcomp h).RelHomotopy (K.postcomp h) where
  level n := (J.level n).compContinuousMap (h.map n)
  comm n r s x t := (congrArg (h.map (n + 1)) (J.comm n r s x t)).trans
    (congrArg (fun p ↦ p t) (h.comm n (J.level n (r, (s, x)))))

end Homotopy.RelHomotopy

end Topology.LoopPrespectrum
