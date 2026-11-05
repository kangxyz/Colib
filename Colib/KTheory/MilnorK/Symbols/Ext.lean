/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.Basic

/-!
# Homogeneous maps are determined by their tuple symbols

These extensionality statements adapt `Aglib.KTheory.MilnorK.Basic.addHom_ext` and
`linearMap_ext` at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The source and target
universes are independent. All objects are the native Stacks homogeneous Milnor K-groups.

The proof uses the existing generation theorem for all list symbols and the native graded
projection. Symbols of a different length project to zero. This avoids importing the
higher-level fixed-length generation theorem from `MilnorNorm.SingleResidue`, and does not
reprove tensor-algebra generation or introduce a second symbol presentation.

The construction is based on the graded tensor-algebra quotient of Stacks Project,
Tag 0EAY, first paragraph.
-/

@[expose] public noncomputable section

universe u v

variable {k : Type u} [Field k] {n : ℕ} {A : Type v} [AddCommGroup A]

/-- Additive maps from one Milnor K-group agree if they agree on its ordered tuple symbols. -/
@[ext] theorem milnorKTheory_addHom_ext (f g : MilnorKTheory k n →+ A)
    (h : ∀ a : Fin n → kˣ, f (milnorKTupleSymbol a) = g (milnorKTupleSymbol a)) :
    f = g := by
  let p : MilnorKRing k →+ MilnorKTheory k n :=
    (DFinsupp.evalAddMonoidHom n).comp
      (DirectSum.decomposeAddEquiv (milnorKGrading k)).toAddMonoidHom
  have hp (x : MilnorKTheory k n) : p x = x := by
    apply Subtype.ext
    exact DirectSum.decompose_of_mem_same (milnorKGrading k) x.2
  let H : AddSubgroup (MilnorKRing k) := (f.comp p).eqLocus (g.comp p)
  have hH (l : List kˣ) : milnorKSymbolProd k l ∈ H := by
    change f (p (milnorKSymbolProd k l)) = g (p (milnorKSymbolProd k l))
    by_cases hl : l.length = n
    · subst n
      have hpl : p (milnorKSymbolProd k l) = milnorKTupleSymbol l.get := by
        apply Subtype.ext
        change (DirectSum.decompose (milnorKGrading k) (milnorKSymbolProd k l) l.length :
          MilnorKRing k) = milnorKSymbolProd k (List.ofFn l.get)
        rw [List.ofFn_get]
        exact DirectSum.decompose_of_mem_same (milnorKGrading k)
          (milnorKSymbolProd_mem_milnorKGrading l)
      rw [hpl]
      exact h l.get
    · have hpl : p (milnorKSymbolProd k l) = 0 := by
        apply Subtype.ext
        exact DirectSum.decompose_of_mem_ne (milnorKGrading k)
          (milnorKSymbolProd_mem_milnorKGrading l) hl
      rw [hpl, map_zero, map_zero]
  apply AddMonoidHom.ext
  intro x
  have hx := milnorKGrading_le_of_forall_milnorKSymbolProd_mem hH n x.2
  change f (p x) = g (p x) at hx
  simpa only [hp] using hx

/-- Integer-linear maps from one Milnor K-group are determined by their tuple symbols. -/
@[ext] theorem milnorKTheory_linearMap_ext (f g : MilnorKTheory k n →ₗ[ℤ] A)
    (h : ∀ a : Fin n → kˣ, f (milnorKTupleSymbol a) = g (milnorKTupleSymbol a)) :
    f = g := by
  apply LinearMap.toAddMonoidHom_injective
  exact milnorKTheory_addHom_ext f.toAddMonoidHom g.toAddMonoidHom h

attribute [colib_tag "COL-0030"] milnorKTheory_addHom_ext milnorKTheory_linearMap_ext

add_to_stacks 0EAY
  "Consequence of the homogeneous tensor quotient: additive maps are determined by tuple symbols"
  milnorKTheory_addHom_ext
add_to_stacks 0EAY
  "Consequence of the homogeneous tensor quotient: integer-linear maps are determined by symbols"
  milnorKTheory_linearMap_ext
