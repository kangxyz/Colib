/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
Image-kernel exactness for actual sequential abelian-group colimits. The proof uses genuine
representatives, eventual equality, and naturality, without injective transition maps or a
stabilization hypothesis.
-/
/-! Implementation provenance:
`Quillen/Aglib/CategoryTheory/Limits/Shapes/SequentialSystem/Exactness.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native filtered
abelian colimit and its representative maps are retained. -/
@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace CategoryTheory.Limits

/-- Actual compatible maps of sequential abelian groups retain image-kernel
exactness after taking their categorical colimits. -/
theorem sequentialColimit_exact {A B C : ℕ ⥤ AddCommGrpCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C)
    (h : ∀ n, Function.Exact (f.app n) (g.app n)) :
    Function.Exact (colimMap f) (colimMap g) := by
  let : PreservesFilteredColimitsOfSize.{0,0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  intro x
  constructor
  · intro hx
    obtain ⟨n,y,rfl⟩ := Concrete.colimit_exists_rep B x
    rw [← ConcreteCategory.comp_apply, ι_colimMap, ConcreteCategory.comp_apply,
      ← map_zero (colimit.ι C n).hom] at hx
    obtain ⟨k,e₁,e₂,hk⟩ := Concrete.colimit_exists_of_rep_eq C _ _ hx
    rw [map_zero, ← ConcreteCategory.comp_apply, ← g.naturality,
      ConcreteCategory.comp_apply] at hk
    obtain ⟨z,hz⟩ := (h k _).mp hk
    refine ⟨colimit.ι A k z, ?_⟩
    rw [← ConcreteCategory.comp_apply, ι_colimMap, ConcreteCategory.comp_apply, hz]
    exact colimit.w_apply B e₁ y
  · rintro ⟨y,rfl⟩
    obtain ⟨n,z,rfl⟩ := Concrete.colimit_exists_rep A y
    change ((colimit.ι A n ≫ colimMap f) ≫ colimMap g) z = 0
    rw [ι_colimMap, Category.assoc, ι_colimMap]
    change (colimit.ι C n) ((g.app n) ((f.app n) z)) = 0
    have hz := (h n ((f.app n) z)).mpr ⟨z,rfl⟩
    rw [hz]
    exact map_zero _

end CategoryTheory.Limits
