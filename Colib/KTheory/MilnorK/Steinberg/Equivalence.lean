/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.Injectivity
public import Colib.KTheory.MilnorK.Steinberg.Surjectivity

/-!
# Matsumoto's theorem for the stable Steinberg kernel in characteristic zero

The forward map is literally `StableSteinberg.milnorToKernel`. Surjectivity uses
all-rank kernel generation; injectivity uses the actual finite Bruhat actions
and their faithful native Milnor coefficient translations. The ordered pair
symbol retains its positive torus-defect normalization. No choice of an
alternative Milnor group or comparison adapter is involved.

The mathematical source is Matsumoto (1969), Section 5, Theorem 5.10 and
Corollary 5.11, pp. 30–31: specialize the non-symplectic presentation over an
infinite field to stable type A. The implementation retains `[CharZero F]`.
Weibel, III, Theorem 6.1 states the classical K₂ form.

The implementation ingredients adapt the pinned Quillen source at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This identifies the elementary
Steinberg kernel. Identification with Quillen's homotopy-defined K₂ is separate.
-/

@[expose] public noncomputable section

universe u v

namespace StableSteinberg

variable (F : Type u) [Field F] [CharZero F]

/-- The canonical native Milnor map is bijective in characteristic zero. -/
theorem milnorToKernel_bijective_charZero : Function.Bijective (milnorToKernel F) :=
  ⟨milnorToKernel_injective_charZero F, KernelGeneration.milnorToKernel_surjective F⟩

/-- Matsumoto's equivalence with the literal native Milnor-to-kernel forward map. -/
@[colib_ref "Matsumoto1969" "Section 5, Theorem 5.10 and Corollary 5.11, pp. 30-31"
    "adaptation" "The non-symplectic symbol presentation specialized to stable type A over \
      characteristic-zero fields; no Quillen homotopy identification is part of this result",
  colib_ref "WeibelKBook" "III, Theorem 6.1" "adaptation"
    "The classical field K2 presentation, implemented with the native Milnor group and \
      stable Steinberg kernel in characteristic zero"]
def milnorKernelEquiv : MilnorKTheory F 2 ≃+ Additive ((toElementary F).ker) :=
  AddEquiv.ofBijective (milnorToKernel F) (milnorToKernel_bijective_charZero F)

lemma milnorKernelEquiv_toAddMonoidHom :
    (milnorKernelEquiv F).toAddMonoidHom = milnorToKernel F := rfl

@[simp] lemma milnorKernelEquiv_apply (a : MilnorKTheory F 2) :
    milnorKernelEquiv F a = milnorToKernel F a := rfl

/-- The equivalence keeps the original ordered positive torus defect. -/
lemma milnorKernelEquiv_pair (a b : Fˣ) :
    milnorKernelEquiv F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (torusDefectKernel a b) :=
  milnorToKernel_pair a b

/-- The inverse sends the actual torus-defect kernel element back to its ordered symbol. -/
lemma milnorKernelEquiv_symm_torusDefectKernel (a b : Fˣ) :
    (milnorKernelEquiv F).symm (Additive.ofMul (torusDefectKernel a b)) =
      milnorKTupleSymbol ![a, b] := by
  apply (milnorKernelEquiv F).injective
  rw [AddEquiv.apply_symm_apply, milnorKernelEquiv_pair]

variable {F} {L : Type v} [Field L] [CharZero L]

/-- The equivalences commute with the existing coefficient maps across universes. -/
lemma milnorKernelEquiv_naturality (f : F →+* L) :
    ((toElementaryKernelMap f).toAdditive).comp (milnorKernelEquiv F).toAddMonoidHom =
      (milnorKernelEquiv L).toAddMonoidHom.comp (milnorKTheoryMap f 2).toAddMonoidHom :=
  milnorToKernel_naturality f

end StableSteinberg
