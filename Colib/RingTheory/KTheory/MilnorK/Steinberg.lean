/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Symbols
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Native Milnor K₂ symbols in the stable elementary kernel

The proved ordered torus defect descends directly from Stacks' homogeneous
`MilnorKTheory F 2`, using its native symbol-map universal property. There is no
intermediate Milnor model or pair-quotient transport. Every ordered pair maps to
`h(a) h(b) h(ab)⁻¹` in the actual kernel, with the original positive sign.
The canonical coefficient maps commute, including across independent universes.

## Implementation provenance

This rewrites the final Milnor-map portion of
`Quillen/Algebra/Group/StableSteinbergSymbols.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd` against the pinned Stacks model.
Surjectivity and characteristic-zero Matsumoto injectivity are proved in later leaves.
The later `QuillenEquivalence` leaf identifies the original Quillen K₂ maps in characteristic zero;
the scalar-action product marking is a separate comparison.
-/
@[expose] public noncomputable section

universe u v

namespace StableSteinberg

open scoped commutatorElement

attribute [local instance] kernelCommGroup

variable {F : Type u} [Field F]

/-- The literal kernel-valued torus defect satisfies the native symbol conditions. -/
theorem torusDefect_isMilnorKSymbolMap :
    IsMilnorKSymbolMap (fun a : Fin 2 → Fˣ =>
      Additive.ofMul (torusDefectKernel (a 0) (a 1))) where
  map_mul a i b c := by
    fin_cases i
    · change torusDefectKernel (b * c) (a 1) =
        torusDefectKernel b (a 1) * torusDefectKernel c (a 1)
      exact Subtype.ext (torusDefect_mul_left b c (a 1))
    · change torusDefectKernel (a 0) (b * c) =
        torusDefectKernel (a 0) b * torusDefectKernel (a 0) c
      exact Subtype.ext (torusDefect_mul_right (a 0) b c)
  steinberg a i j hij hab := by
    have hi : i = 0 := by omega
    have hj : j = 1 := by omega
    subst i
    subst j
    change torusDefectKernel (a 0) (a 1) = 1
    exact Subtype.ext (torusDefect_steinberg (a 0) (a 1) hab)

/-- The canonical native Milnor map, with no change of Milnor presentation. -/
def milnorToKernel (F : Type u) [Field F] :
    MilnorKTheory F 2 →+ Additive ((toElementary F).ker) :=
  torusDefect_isMilnorKSymbolMap.lift.toAddMonoidHom

/-- Ordered tuple symbols retain their exact original kernel word. -/
@[simp] lemma milnorToKernel_symbol (a : Fin 2 → Fˣ) :
    milnorToKernel F (milnorKTupleSymbol a) =
      Additive.ofMul (torusDefectKernel (a 0) (a 1)) :=
  torusDefect_isMilnorKSymbolMap.lift_symbol a

/-- The canonical map preserves the ordered pair and its positive normalization. -/
lemma milnorToKernel_pair (a b : Fˣ) :
    milnorToKernel F (milnorKTupleSymbol ![a, b]) = Additive.ofMul (torusDefectKernel a b) :=
  milnorToKernel_symbol ![a, b]

variable {L : Type v} [Field L]

/-- The native Milnor map commutes with the actual field change on the kernel. -/
lemma milnorToKernel_naturality (f : F →+* L) :
    ((toElementaryKernelMap f).toAdditive).comp (milnorToKernel F) =
      (milnorToKernel L).comp (milnorKTheoryMap f 2).toAddMonoidHom := by
  apply milnorKTheory_addHom_ext
  intro a
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    milnorToKernel_symbol, milnorKTheoryMap_tupleSymbol]
  change Additive.ofMul (toElementaryKernelMap f (torusDefectKernel (a 0) (a 1))) =
    Additive.ofMul (torusDefectKernel (Units.map f.toMonoidHom (a 0))
      (Units.map f.toMonoidHom (a 1)))
  exact congrArg Additive.ofMul (toElementaryKernelMap_torusDefectKernel f (a 0) (a 1))

/-- In a common universe, naturality uses the literal pinned Stacks transport. -/
lemma milnorToKernel_naturality_transport {K : Type u} [Field K] (f : F →+* K) :
    ((toElementaryKernelMap f).toAdditive).comp (milnorToKernel F) =
      (milnorToKernel K).comp (milnorKTransport f 2) := by
  apply AddMonoidHom.ext
  intro x
  have h := DFunLike.congr_fun (milnorToKernel_naturality f) x
  simpa only [AddMonoidHom.comp_apply, milnorKTheoryMap_eq_transport,
    LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_toIntLinearMap] using h

/-- The literal torus defect inherits skew symmetry from native Milnor symbols. -/
lemma torusDefect_skew (a b : Fˣ) : torusDefect a b = (torusDefect b a)⁻¹ := by
  have hs : milnorKTupleSymbol ![a, b] = -milnorKTupleSymbol ![b, a] := by
    have hu : Function.update (Function.update ![a, b] 0 b) 1 a = ![b, a] := by
      ext i
      fin_cases i <;> simp
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hu] using
      milnorKTupleSymbol_adjacent_skew ![a, b] 0 1 rfl
  have hh := congrArg (milnorToKernel F) hs
  rw [map_neg, milnorToKernel_pair, milnorToKernel_pair] at hh
  change torusDefectKernel a b = (torusDefectKernel b a)⁻¹ at hh
  exact congrArg (fun z : (toElementary F).ker => (z : Group F)) hh

/-- The original ordered defect is the positive rank-three torus commutator. -/
lemma commutator_h_h02 (a b : Fˣ) : ⁅h a, h02 b⁆ = torusDefect a b := by
  rw [commutator_torus]
  exact (torusDefect_skew a b).symm

end StableSteinberg

attribute [colib_ref "quillen" "Quillen/Algebra/Group/StableSteinbergSymbols.lean, milnorToKernel"
  "adaptation" "Direct descent from the native Stacks degree-two Milnor group; same ordered defect"]
  StableSteinberg.milnorToKernel
attribute [colib_ref "quillen"
  "Quillen/Algebra/Group/StableSteinbergSymbols.lean, milnorToKernel_pair"
  "adaptation" "The ordered pair retains the positive original kernel word h(a) h(b) h(ab)^(-1)"]
  StableSteinberg.milnorToKernel_pair
attribute [colib_ref "quillen"
  "Quillen/Algebra/Group/StableSteinbergSymbols.lean, milnorToKernel_naturality"
  "adaptation" "Coefficient maps commute; common-universe transport is the literal Stacks map"]
  StableSteinberg.milnorToKernel_naturality StableSteinberg.milnorToKernel_naturality_transport
attribute [colib_ref "quillen" "Quillen/Algebra/Group/StableSteinbergSymbols.lean, commutator_h_h02"
  "adaptation" "The original ordered defect equals the positive rank-three torus commutator"]
  StableSteinberg.commutator_h_h02

attribute [colib_tag "COL-0255"] StableSteinberg.milnorToKernel
  StableSteinberg.milnorToKernel_pair StableSteinberg.milnorToKernel_naturality
  StableSteinberg.milnorToKernel_naturality_transport StableSteinberg.commutator_h_h02
