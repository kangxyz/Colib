/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.Relations
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Multilinearity of proposed Milnor symbol maps

`IsMilnorKSymbolMap` is a property of a proposed tuple-valued function, not a new model of
Milnor K-theory. It retains the coordinate and adjacent Steinberg conditions of
`Aglib.KTheory.MilnorK.Basic.IsSymbolMap` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, with independent source and target universes.
-/

@[expose] public noncomputable section

universe u v

variable {k : Type u} [Field k] {n : ℕ} {A : Type v} [AddCommGroup A]

/-- The defining coordinate-additivity and adjacent Steinberg conditions on a symbol function. -/
structure IsMilnorKSymbolMap (s : (Fin n → kˣ) → A) : Prop where
  map_mul : ∀ (a : Fin n → kˣ) (i : Fin n) (b c : kˣ),
    s (Function.update a i (b * c)) =
      s (Function.update a i b) + s (Function.update a i c)
  steinberg : ∀ (a : Fin n → kˣ) (i j : Fin n),
    i.val + 1 = j.val → (a i : k) + (a j : k) = 1 → s a = 0

namespace IsMilnorKSymbolMap

variable {s : (Fin n → kˣ) → A} (hs : IsMilnorKSymbolMap s)

/-- Fixing all other coordinates gives an additive homomorphism from the additive unit group. -/
def coordinateAddHom (a : Fin n → kˣ) (i : Fin n) : Additive kˣ →+ A where
  toFun b := s (Function.update a i b.toMul)
  map_zero' := by
    have h := hs.map_mul a i 1 1
    rw [one_mul] at h
    exact (add_left_cancel ((add_zero _).trans h)).symm
  map_add' b c := hs.map_mul a i b.toMul c.toMul

/-- Reading the unit group additively makes a proposed symbol map integer-multilinear. -/
def toMultilinear : MultilinearMap ℤ (fun _ : Fin n => Additive kˣ) A :=
  MultilinearMap.mk' (fun a => s (Additive.toMul ∘ a))
    (fun a i b c => by
      simpa [Function.comp_update, coordinateAddHom] using
        (hs.coordinateAddHom (Additive.toMul ∘ a) i).map_add b c)
    (fun a i z b => by
      simpa [Function.comp_update, coordinateAddHom] using
        (hs.coordinateAddHom (Additive.toMul ∘ a) i).map_zsmul z b)

/-- The multilinear map has exactly the original tuple values. -/
@[simp] theorem toMultilinear_apply (a : Fin n → Additive kˣ) :
    hs.toMultilinear a = s (Additive.toMul ∘ a) := rfl

end IsMilnorKSymbolMap

/-- Native homogeneous symbols satisfy the proposed-symbol-map conditions. -/
theorem milnorKTupleSymbol_isSymbolMap :
    IsMilnorKSymbolMap (milnorKTupleSymbol (k := k) (n := n)) :=
  ⟨milnorKTupleSymbol_update_mul, milnorKTupleSymbol_steinberg⟩

attribute [colib_tag "COL-0042"] IsMilnorKSymbolMap milnorKTupleSymbol_isSymbolMap

add_to_stacks 0EAY
  "Construction background only: coordinate additivity and Steinberg relations of native symbols"
  IsMilnorKSymbolMap
