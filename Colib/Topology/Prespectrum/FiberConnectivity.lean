/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.FiberSequence

/-!
The negative-one stable fiber obstruction is controlled by the actual degree-zero surjectivity
hypothesis.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberConnectivity.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual fiber coordinates, strict
structure maps, specified whole nullhomotopies, integer grading and connecting signs
are retained. -/
@[expose] public section


noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- A zero source group and surjectivity in the preceding target degree force
the actual stable fiber group to vanish. -/
theorem stableFiber_subsingleton_of_source_zero_of_surjective (d : ℤ)
    (hE : Subsingleton (stableHomotopyGroup E d))
    (hf : Function.Surjective ((stableHomotopyFunctor (d + 1)).map f)) :
    Subsingleton (stableHomotopyGroup (homotopyFiber f) d) := by
  have hδ (b : stableHomotopyGroup F (d+1)) : stableFiberConnecting f d b = 0 := by
    apply (stableFiberConnecting_exact_target f d b).mpr
    exact hf b
  have hz (z : stableHomotopyGroup (homotopyFiber f) d) : z = 0 := by
    obtain ⟨b,hb⟩ := (stableFiberConnecting_exact_fiber f d z).mp (hE.elim _ _)
    rw [← hb,hδ]
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

/-- Fibers of connective spectra remain connective under the relevant
surjective degree-zero map. The negative-one term uses that actual hypothesis. -/
theorem stableFiber_neg_subsingleton_of_connective
    (hE : ∀ d : ℤ, d < 0 → Subsingleton (stableHomotopyGroup E d))
    (hF : ∀ d : ℤ, d < 0 → Subsingleton (stableHomotopyGroup F d))
    (h0 : Function.Surjective ((stableHomotopyFunctor 0).map f))
    (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup (homotopyFiber f) d) := by
  apply stableFiber_subsingleton_of_source_zero_of_surjective f d (hE d hd)
  by_cases he : d+1 = 0
  · rw [he]; exact h0
  · have hz := hF (d+1) (by omega)
    intro y
    exact ⟨0,hz.elim _ _⟩
end Topology.LoopPrespectrum
