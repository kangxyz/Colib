/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Original sequential colimit maps from eventual component isomorphisms

A natural transformation of sequential abelian groups induces an isomorphism on the unchanged
categorical colimits if its original components are isomorphisms after a finite stage. The proof
uses actual representatives, eventual equality and original naturality, without replacing either
diagram or selecting a new transition map.
-/
/-! Implementation provenance:
`Quillen/Aglib/CategoryTheory/Limits/Shapes/SequentialSystem/EventuallyIso.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This uses native Mathlib diagrams, colimits and original naturality, with no Aglib import. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace CategoryTheory.Limits.SequentialSystem

/-- Eventual component isomorphisms suffice for the actual original sequential colimit map. -/
theorem isIso_colimMap_of_eventually {F G : ℕ ⥤ AddCommGrpCat.{u}}
    (a : F ⟶ G) (N : ℕ) (ha : ∀ n, N ≤ n → IsIso (a.app n)) : IsIso (colimMap a) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have hrep (i : ℕ) (x : F.obj i) :
      colimMap a (colimit.ι F i x) = colimit.ι G i (a.app i x) :=
    ConcreteCategory.congr_hom (ι_colimMap a i) x
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep F x
    obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep F y
    rw [hrep, hrep] at hxy
    obtain ⟨k, hi, hj, hk⟩ := Concrete.colimit_exists_of_rep_eq G _ _ hxy
    let l := max k N
    let hkl : k ⟶ l := homOfLE (le_max_left k N)
    let := ha l (le_max_right k N)
    have he : a.app l (F.map (hi ≫ hkl) x) = a.app l (F.map (hj ≫ hkl) y) := by
      rw [← ConcreteCategory.comp_apply, a.naturality,
        ← ConcreteCategory.comp_apply, a.naturality]
      change G.map (hi ≫ hkl) (a.app i x) = G.map (hj ≫ hkl) (a.app j y)
      rw [Functor.map_comp, Functor.map_comp]
      exact congrArg (G.map hkl) hk
    have h := (ConcreteCategory.bijective_of_isIso (a.app l)).injective he
    exact (colimit.w_apply F (hi ≫ hkl) x).symm.trans
      ((congrArg (colimit.ι F l) h).trans (colimit.w_apply F (hj ≫ hkl) y))
  · intro y
    obtain ⟨i, y, rfl⟩ := Concrete.colimit_exists_rep G y
    let j := max i N
    let hij : i ⟶ j := homOfLE (le_max_left i N)
    let := ha j (le_max_right i N)
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (a.app j)).surjective (G.map hij y)
    refine ⟨colimit.ι F j x, ?_⟩
    rw [hrep, hx]
    exact colimit.w_apply G hij y

end CategoryTheory.Limits.SequentialSystem
