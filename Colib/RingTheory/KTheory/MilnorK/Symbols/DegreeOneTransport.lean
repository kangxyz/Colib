/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.RingTransport
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeOne

/-!
# Cross-universe naturality of the native first Milnor group

This is the independent-universe version of the pinned native degree-one transport formula.
Both group identifications and field maps are the existing ones; the ring transport comparison
connects them without exposing the implementation of the native degree-one equivalence.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

/-- The native degree-one identification commutes with cross-universe field transport. -/
theorem milnorKTheoryOneAddEquiv_map {k : Type u} {K : Type v} [Field k] [Field K]
    (f : k →+* K) (x : MilnorKTheory k 1) :
    milnorKTheoryOneAddEquiv K (milnorKTheoryMap f 1 x) =
      Additive.ofMul (Units.map f.toMonoidHom (milnorKTheoryOneAddEquiv k x).toMul) := by
  apply (milnorKTheoryOneAddEquiv K).symm.injective
  apply Subtype.ext
  rw [AddEquiv.symm_apply_apply, ← milnorKRingMapLift_coe,
    coe_milnorKTheoryOneAddEquiv_symm]
  have hx : (x : MilnorKRing k) =
      milnorKSymbol k (milnorKTheoryOneAddEquiv k x).toMul := by
    simpa only [AddEquiv.symm_apply_apply, milnorKSymbol_eq_mk', ofMul_toMul] using
      coe_milnorKTheoryOneAddEquiv_symm k (milnorKTheoryOneAddEquiv k x)
  rw [hx, milnorKRingMapLift_symbol]
  rfl

end Stacks.Chow
