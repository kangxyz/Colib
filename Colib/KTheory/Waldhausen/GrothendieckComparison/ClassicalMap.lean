/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberRelations
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectCompatibility

/-! # The original classical presentation embeds naturally in fine Waldhausen K₀

The original object loops satisfy the chosen-zero, weak-arrow and displayed
cofibration-pushout relations by genuine geometric and structural additivity
proofs. Their canonical homomorphism is split injective via the already-proved
original grading map. Generation of all topological K₀ classes remains separate.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/ClassicalMap.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The original object-loop classes extend over precisely the original
classical weak-equivalence and cofibration-pushout presentation. -/
def grothendieckToKZero : Multiplicative (Group W) →* W.K 0 := by
  let : CommGroup (W.K 0) := Additivity.KCommGroup W 0
  let d : Cofinality.Grading W (Additive (W.K 0)) := {
    value := fun A ↦ Additive.ofMul (W.kZeroObjectClass A)
    zero := by
      change W.kZeroObjectClass W.zero = 1
      exact W.kZeroObjectClass_zero
    weak := by
      intro A B f hf
      change W.kZeroObjectClass A = W.kZeroObjectClass B
      exact W.kZeroObjectClass_weak f hf
    pushout := by
      intro A B D Q i f g j hi hQ
      change W.kZeroObjectClass Q =
        (W.kZeroObjectClass B * W.kZeroObjectClass D) / W.kZeroObjectClass A
      simpa only [div_eq_mul_inv] using W.kZeroObjectClass_pushout hi hQ }
  exact AddMonoidHom.toMultiplicativeLeft (lift W d)

/-- The canonical forward homomorphism sends each original algebraic generator
to the exact original topological object loop. -/
@[simp] theorem grothendieckToKZero_objectClass (A : C) :
    grothendieckToKZero W (Multiplicative.ofAdd (objectClass W A)) = W.kZeroObjectClass A := by
  simp [grothendieckToKZero, AddMonoidHom.toMultiplicativeLeft]

/-- Original algebraic generators determine maps to any group, without a
commutativity assumption on that target. -/
@[ext] theorem mulHom_ext {H : Type v} [_root_.Group H]
    (f g : Multiplicative (Group W) →* H)
    (h : ∀ A, f (Multiplicative.ofAdd (objectClass W A)) =
      g (Multiplicative.ofAdd (objectClass W A))) : f = g := by
  apply MonoidHom.ext
  intro a
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk'_surjective (relations W) a.toAdd
  change f (Multiplicative.ofAdd a.toAdd) = g (Multiplicative.ofAdd a.toAdd)
  rw [← hr]
  clear hr a
  induction r using FreeAbelianGroup.induction_on with
  | zero => simp
  | of A => exact h A
  | neg r ih => simp only [map_neg, ofAdd_neg, map_inv, ih]
  | add r s hr hs => simp only [map_add, ofAdd_add, map_mul, hr, hs]

/-- The actual homotopical-to-classical map is a left inverse of the canonical
original object-class comparison. -/
@[simp] theorem kZeroToGrothendieck_comp :
    (kZeroToGrothendieck W).comp (grothendieckToKZero W) = MonoidHom.id _ := by
  apply mulHom_ext W
  intro A
  simp

/-- The original classical comparison is injective into the actual fine Waldhausen K₀. -/
theorem grothendieckToKZero_injective : Function.Injective (grothendieckToKZero W) := by
  intro a b hab
  have h := congrArg (kZeroToGrothendieck W) hab
  simpa only [← MonoidHom.comp_apply, kZeroToGrothendieck_comp, MonoidHom.id_apply] using h

variable {D : Type u} [SmallCategory D] (V : Structure D) (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The canonical forward object-class homomorphism respects the original exact-functor maps. -/
theorem grothendieckToKZero_natural :
    (KMap hF 0).comp (grothendieckToKZero W) =
      (grothendieckToKZero V).comp (map W F hF).toMultiplicative := by
  apply mulHom_ext W
  intro A
  simp

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
