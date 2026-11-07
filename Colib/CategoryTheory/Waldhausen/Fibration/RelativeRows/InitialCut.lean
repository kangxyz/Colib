/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.TailSection
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.IsomorphicSources

/-! # The original initial cutoff subrow

Collapse all tail vertices to the first tail vertex. The resulting row maps
to the original row through its actual interval maps. The genuine row
cofibration condition is proved on every horizontal triple, including all
degenerate and zero-source cases.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/InitialCut.lean`
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

/-- The original added vertex remains0, while every tail vertex becomes1. -/
def cutIndex (n : SimplexCategory) : addInitial.obj n ⟶ addInitial.obj n :=
  addInitial.map (SimplexCategory.const n n 0)

theorem cutIndex_le (n : SimplexCategory) (i : Fin ((addInitial.obj n).len + 1)) :
    (cutIndex n).toOrderHom i ≤ i := by
  change Fin (n.len + 1 + 1) at i
  cases i using Fin.cases with
  | zero => exact le_rfl
  | succ i => exact Nat.succ_le_succ (Fin.zero_le i)

/-- The actual inclusion of each cutoff interval into the original interval. -/
def cutIndexToId (n : SimplexCategory) : QuotientRows.indexMap (cutIndex n) ⟶ 𝟭 (Interval
    (addInitial.obj n)) where
  app p := homOfLE ⟨cutIndex_le n p.val.1, cutIndex_le n p.val.2⟩
  naturality _ _ _ := Subsingleton.elim _ _

/-- The original cutoff is an actual outer ordinal restriction, hence genuinely exact. -/
def cutFunctor (n : SimplexCategory) : Obj N n ⥤ Obj N n := reindex N (SimplexCategory.const n n 0)

theorem cutFunctor_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
      (waldhausenStructure N n).cof (waldhausenStructure N n).weq (cutFunctor N n) :=
  reindex_exact N (SimplexCategory.const n n 0)

/-- The original component inclusion from the actual cutoff row. -/
def cutToId (n : SimplexCategory) : cutFunctor N n ⟶ 𝟭 (Obj N n) where
  app X := (objects N n).homMk ((QuotientRows.objects V (addInitial.obj n)).homMk
    (Functor.whiskerRight (cutIndexToId n) X.obj.obj))
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    ext p
    exact (f.hom.hom.naturality ((cutIndexToId n).app p)).symm

/-- The cutoff inclusion is a genuine row cofibration, using its actual relative squares. -/
theorem cutToId_cof (n : SimplexCategory) (X : Obj N n) :
    (waldhausenStructure N n).cof ((cutToId N n).app X) := by
  intro i j k hij hjk
  change Fin (n.len + 1 + 1) at i j k
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      let : IsIso (Arrow.Hom.left ((QuotientRows.horizontalArrow V 0 0 k hij hjk).map
          ((forget N n).map ((cutToId N n).app X))).hom) := by
        change IsIso (X.obj.obj.map (𝟙 (interval 0 0 le_rfl)))
        infer_instance
      cases k using Fin.cases with
      | zero =>
        apply ExtensionCategory.cof_of_left_isIso V
        exact V.cof_iso _ (inferInstance : IsIso (X.obj.obj.map (𝟙 (interval 0 0 le_rfl))))
      | succ k =>
        apply ExtensionCategory.cof_of_left_isIso V
        exact X.obj.property.cofibration 0 (0 : Fin (n.len + 1)).succ k.succ
          (Fin.zero_le _) (Nat.succ_le_succ (Fin.zero_le k))
    | succ j =>
      cases k using Fin.cases with
      | zero => have h : j.val + 1 ≤ 0 := hjk; omega
      | succ k =>
        let : IsIso ((QuotientRows.horizontalArrow V 0 j.succ k.succ hij hjk).obj
            ((forget N n).obj ((cutFunctor N n).obj X))).obj.hom := by
          change IsIso (X.obj.obj.map (𝟙 (interval 0 (0 : Fin (n.len + 1)).succ (Fin.zero_le _))))
          infer_instance
        apply ExtensionCategory.cof_of_top_isIso V
        exact X.obj.property.cofibration 0 (0 : Fin (n.len + 1)).succ j.succ
          (Fin.zero_le _) (Nat.succ_le_succ (Fin.zero_le j))
  | succ i =>
    cases j using Fin.cases with
    | zero => have h : i.val + 1 ≤ 0 := hij; omega
    | succ j =>
      cases k using Fin.cases with
      | zero => have h : j.val + 1 ≤ 0 := hjk; omega
      | succ k =>
        apply Structure.cof_of_isZero (ExtensionCategory.waldhausenStructure V)
        exact ExtensionCategory.isZero_of_components V _
          (X.obj.property.zero (0 : Fin (n.len + 1)).succ)
          (X.obj.property.zero (0 : Fin (n.len + 1)).succ)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
