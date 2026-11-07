/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.UniverseHomotopy
public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescope

/-! # Homotopy equivalences for original endofunctor iterates -/

/-!
Implementation provenance: adapted from
`Quillen/Topology/ClassifyingSpace/EndofunctorIterationHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.Grothendieck.EndofunctorTelescope
variable {C : Type u} [Category.{v} C] (T : C ⥤ C)

/-- Iterate the specified genuine classifying-space homotopy equivalence. -/
def iterateClassifyingHomotopyEquiv
    (e : ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace C)) :
    ℕ → ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace C)
  | 0 => ContinuousMap.HomotopyEquiv.refl _
  | n + 1 => (iterateClassifyingHomotopyEquiv e n).trans e

/-- The forward map of the iterated equivalence is precisely the realized original iterate. -/
theorem iterateClassifyingHomotopyEquiv_toFun
    (e : ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace C))
    (he : e.toFun = classifyingSpaceMapUniversal T) (n : ℕ) :
    (iterateClassifyingHomotopyEquiv e n).toFun =
      classifyingSpaceMapUniversal (iterate T n) := by
  induction n with
  | zero =>
    change ContinuousMap.id _ = classifyingSpaceMapUniversal (𝟭 C)
    rw [classifyingSpaceMapUniversal_id]
  | succ n ih =>
    change e.toFun.comp (iterateClassifyingHomotopyEquiv e n).toFun =
      classifyingSpaceMapUniversal (iterate T n ⋙ T)
    rw [ih, he, classifyingSpaceMapUniversal_comp]

end CategoryTheory.Grothendieck.EndofunctorTelescope
