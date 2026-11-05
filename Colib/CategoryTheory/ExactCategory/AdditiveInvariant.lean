/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Basic

/-!
# Conflation-additive object invariants

Additivity on actual conflations implies isomorphism invariance and vanishing
on every zero object. No group presentation or K-theory model is used.

## Implementation provenance

Adapted from `Quillen/Aglib/CategoryTheory/ExactCategory/AdditiveInvariant.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving conflation additivity,
isomorphism invariance, vanishing on the chosen zero object and their hypotheses.
-/
@[expose] public section

noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- A function on objects is a conflation-additive invariant if it takes a middle
object to the sum of the two outer objects for every conflation. -/
def IsAdditiveInvariant {A : Type w} [AddCommGroup A] (f : C → A) : Prop :=
  ∀ (S : ShortComplex C), E.conflation S → f S.X₂ = f S.X₁ + f S.X₃

variable {A : Type w} [AddCommGroup A]

/-- Conflation additivity alone implies isomorphism invariance. -/
lemma IsAdditiveInvariant.iso {f : C → A} (hf : E.IsAdditiveInvariant f)
    {X Y : C} (e : X ≅ Y) : f X = f Y := by
  obtain ⟨Z, p, h, hS⟩ := E.inflation_id X
  have hp : p = 0 := by simpa using h
  let T := ShortComplex.mk e.hom (0 : Y ⟶ Z) (by simp)
  have hT : E.conflation T := E.iso_closed
    (ShortComplex.isoMk (Iso.refl X) e (Iso.refl Z) (by simp [T]) (by simp [T, hp])) hS
  exact (hf _ hS).trans (hf _ hT).symm

open ZeroObject in
/-- An additive invariant necessarily vanishes on the zero object. -/
lemma IsAdditiveInvariant.zero {f : C → A} (hf : E.IsAdditiveInvariant f) :
    f (0 : C) = 0 := by
  obtain ⟨Z, p, h, hS⟩ := E.inflation_id (0 : C)
  have hZ : IsZero Z := CokernelCofork.IsColimit.isZero_of_epi
    (E.cokernel (ShortComplex.mk (𝟙 (0 : C)) p h) hS)
  have hz := IsAdditiveInvariant.iso E hf (hZ.iso (isZero_zero C))
  have hadd := hf _ hS
  change f (0 : C) = f (0 : C) + f Z at hadd
  rw [hz] at hadd
  exact add_left_cancel (a := f (0 : C))
    (hadd.symm.trans (add_zero _).symm)

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_ref "WeibelKBook" "II, Definition 7.1 and Universal Property 6.1.2"
  "adaptation" "Conflation-additive functions on objects with values in an abelian group"]
  CategoryTheory.ExactCategory.ExactStructure.IsAdditiveInvariant
