/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Tail

/-! # The actual zero-first section of the acyclic tail

Duplicate the initial vertex of an actual acyclic quotient row. The resulting
one-longer row is a genuine relative row, and every original tail object and
map is retained. Exactness is derived from the actual inclusion and actual
ordinal restriction.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/TailSection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Duplicate the first original vertex: the added0 and original0 both map to0. -/
def dropInitial (n : SimplexCategory) : addInitial.obj n ⟶ n :=
  SimplexCategory.Hom.mk {
    toFun := Fin.cases 0 id
    monotone' := by
      intro i j h
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => have h' : i.val + 1 ≤ 0 := h; omega
        | succ j => exact Nat.le_of_succ_le_succ h }

@[simp] theorem dropInitial_zero (n : SimplexCategory) : (dropInitial n).toOrderHom 0 = 0 := rfl
@[simp] theorem dropInitial_succ (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (dropInitial n).toOrderHom i.succ = i := rfl
@[simp] theorem tail_dropInitial (n : SimplexCategory) : tail.app n ≫ dropInitial n = 𝟙 n := by
  ext i : 3
  rfl

/-- The actual ambient one-longer row obtained by duplicating the first acyclic vertex. -/
def tailSectionUnderlying (n : SimplexCategory) :
    QuotientRows.Obj (acyclicStructure N) n ⥤ QuotientRows.Obj V (addInitial.obj n) :=
  QuotientRows.postcompose (acyclicStructure N) V (acyclicInclusion_exact N) n ⋙
    QuotientRows.reindex V (dropInitial n)

theorem tailSectionUnderlying_mem (n : SimplexCategory) (X : QuotientRows.Obj (acyclicStructure
    N) n) :
    objects N n ((tailSectionUnderlying N n).obj X) := by
  intro p
  exact (X.obj.obj p).property

/-- The actual zero-first section of the original acyclic-tail projection. -/
def tailSection (n : SimplexCategory) : QuotientRows.Obj (acyclicStructure N) n ⥤ Obj N n :=
  (objects N n).lift (tailSectionUnderlying N n) (tailSectionUnderlying_mem N n)

@[simp] theorem tailSection_forget (n : SimplexCategory) :
    tailSection N n ⋙ forget N n = tailSectionUnderlying N n := rfl

/-- This original section is genuinely exact for the original inherited fine classes. -/
theorem tailSection_exact (n : SimplexCategory) :
    IsExact (QuotientRows.waldhausenStructure (acyclicStructure N) n).cof
      (QuotientRows.waldhausenStructure (acyclicStructure N) n).weq
      (waldhausenStructure N n).cof (waldhausenStructure N n).weq (tailSection N n) where
  zero h := IsZero.of_full_of_faithful_of_isZero (forget N n) _
    (((QuotientRows.postcompose_exact _ _ (acyclicInclusion_exact N) n).comp
      (QuotientRows.reindex_exact V (dropInitial n))).zero h)
  cofibration f hf := ((QuotientRows.postcompose_exact _ _ (acyclicInclusion_exact N) n).comp
    (QuotientRows.reindex_exact V (dropInitial n))).cofibration f hf
  weak f hf := ((QuotientRows.postcompose_exact _ _ (acyclicInclusion_exact N) n).comp
    (QuotientRows.reindex_exact V (dropInitial n))).weak f hf
  pushout hf h := IsPushout.of_map_of_faithful (forget N n)
    (((QuotientRows.postcompose_exact _ _ (acyclicInclusion_exact N) n).comp
      (QuotientRows.reindex_exact V (dropInitial n))).pushout hf h)

/-- The actual zero-first section followed by tail retains the original row strictly. -/
@[simp] theorem tailSection_tail (n : SimplexCategory) :
    tailSection N n ⋙ tailFunctor N n = 𝟭 (QuotientRows.Obj (acyclicStructure N) n) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The section's first object is the actual original diagonal zero object. -/
theorem tailSection_first_isZero (n : SimplexCategory) (X : QuotientRows.Obj (acyclicStructure
    N) n) :
    IsZero ((first N n).obj ((tailSection N n).obj X)) :=
  (acyclicInclusion_exact N).zero (X.property.zero 0)

/-- The actual section retains the actual chosen relative zero row. -/
@[simp] theorem tailSection_zero (n : SimplexCategory) :
    (tailSection N n).obj (QuotientRows.zero (acyclicStructure N) n) = zero N n := by
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
