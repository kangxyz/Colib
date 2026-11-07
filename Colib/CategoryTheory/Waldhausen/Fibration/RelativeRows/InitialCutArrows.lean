/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.InitialCut
public import Colib.CategoryTheory.Waldhausen.Rows.ReedyArrows
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.IsomorphicSourceCubes

/-! # The actual cutoff arrow and its original component cofibrations

The cutoff is regarded as an actual Reedy arrow between relative rows.
Its component arrow row retains the original cutoff and original maps.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/InitialCutArrows.lean`
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

/-- The original cutoff inclusion as an actual cofibration-arrow-valued functor. -/
def cutArrow (n : SimplexCategory) : Obj N n ⥤ ExtensionCategory.Obj (waldhausenStructure N n) where
  obj X := ⟨Arrow.mk ((cutToId N n).app X), cutToId_cof N n X⟩
  map f := (ExtensionCategory.objects _).homMk
    (Arrow.homMk ((cutFunctor N n).map f) f ((cutToId N n).naturality f))
  map_id _ := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> simp
  map_comp _ _ := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> simp

/-- Forget only the proved tail-acyclicity, retaining the original cutoff arrow. -/
def ambientCutArrow (n : SimplexCategory) :
    Obj N n ⥤ ExtensionCategory.Obj (QuotientRows.waldhausenStructure V (addInitial.obj n)) :=
  cutArrow N n ⋙ ExtensionCategory.postcompose (waldhausenStructure N n)
    (QuotientRows.waldhausenStructure V (addInitial.obj n)) (forget_exact N n)

/-- The original component-cofibration row of the cutoff. -/
def cutArrowRows (n : SimplexCategory) :
    Obj N n ⥤ QuotientRows.Obj (ExtensionCategory.waldhausenStructure V) (addInitial.obj n) :=
  ambientCutArrow N n ⋙ QuotientRows.reedyToRows V (addInitial.obj n)

/-- Every component square is genuinely Reedy cofibrant under an original row cofibration. -/
theorem cutArrowRows_map_app_cof {n : SimplexCategory} {X Y : Obj N n} (f : X ⟶ Y)
    (hf : (waldhausenStructure N n).cof f) (p : Interval (addInitial.obj n)) :
    ExtensionCategory.cof V (((cutArrowRows N n).map f).hom.app p) := by
  rcases p with ⟨⟨i,j⟩, hij⟩
  change Fin (n.len + 1 + 1) at i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      refine @ExtensionCategory.cof_of_top_isIso _ _ V _ _ _ ?_
        (QuotientRows.cof_app V hf (interval 0 0 le_rfl))
      change IsIso (X.obj.obj.map (𝟙 (interval 0 0 le_rfl)))
      infer_instance
    | succ j =>
      exact hf 0 (0 : Fin (n.len+1)).succ j.succ (Fin.zero_le _)
        (Nat.succ_le_succ (Fin.zero_le j))
  | succ i =>
    cases j using Fin.cases with
    | zero => have h : i.val + 1 ≤ 0 := hij; omega
    | succ j =>
      apply ExtensionCategory.cof_of_zero_sources V
      · exact X.obj.property.zero (0 : Fin (n.len+1)).succ
      · exact Y.obj.property.zero (0 : Fin (n.len+1)).succ
      · exact QuotientRows.cof_app V hf (interval i.succ j.succ hij)

/-- All original horizontal cube tests are genuine relative cofibrations. -/
theorem cutArrowRows_map_cof {n : SimplexCategory} {X Y : Obj N n} (f : X ⟶ Y)
    (hf : (waldhausenStructure N n).cof f) :
    QuotientRows.cof (ExtensionCategory.waldhausenStructure V) (addInitial.obj n)
      ((cutArrowRows N n).map f) := by
  intro i j k hij hjk
  change Fin (n.len + 1 + 1) at i j k
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      let : IsIso ((((QuotientRows.horizontalArrow (ExtensionCategory.waldhausenStructure V)
          0 0 k hij hjk).map ((cutArrowRows N n).map f))).hom.left) :=
        (((cutArrowRows N n).obj X).property.zero 0).isIso
          (((cutArrowRows N n).obj Y).property.zero 0) _
      apply ExtensionCategory.cof_of_left_isIso (ExtensionCategory.waldhausenStructure V)
      exact cutArrowRows_map_app_cof N f hf (interval 0 k (hij.trans hjk))
    | succ j =>
      cases k using Fin.cases with
      | zero => have h : j.val + 1 ≤ 0 := hjk; omega
      | succ k =>
        let : IsIso ((QuotientRows.horizontalArrow (ExtensionCategory.waldhausenStructure V)
            0 j.succ k.succ hij hjk).obj ((cutArrowRows N n).obj X)).obj.hom.hom.left := by
          change IsIso (X.obj.obj.map (𝟙 (interval 0 (0 : Fin (n.len+1)).succ (Fin.zero_le _))))
          infer_instance
        let : IsIso ((QuotientRows.horizontalArrow (ExtensionCategory.waldhausenStructure V)
            0 j.succ k.succ hij hjk).obj ((cutArrowRows N n).obj Y)).obj.hom.hom.left := by
          change IsIso (Y.obj.obj.map (𝟙 (interval 0 (0 : Fin (n.len+1)).succ (Fin.zero_le _))))
          infer_instance
        apply ExtensionCategory.cof_cube_of_horizontal_left_isIso V
        · exact cutArrowRows_map_app_cof N f hf (interval 0 j.succ hij)
        · exact hf 0 j.succ k.succ hij hjk
  | succ i =>
    cases j using Fin.cases with
    | zero => have h : i.val + 1 ≤ 0 := hij; omega
    | succ j =>
      cases k using Fin.cases with
      | zero => have h : j.val + 1 ≤ 0 := hjk; omega
      | succ k =>
        let : IsIso ((QuotientRows.horizontalArrow (ExtensionCategory.waldhausenStructure V)
            i.succ j.succ k.succ hij hjk).obj ((cutArrowRows N n).obj X)).obj.hom.hom.left := by
          change IsIso (X.obj.obj.map (𝟙 (interval (0 : Fin (n.len+1)).succ (0 : Fin
            (n.len+1)).succ le_rfl)))
          infer_instance
        let : IsIso ((QuotientRows.horizontalArrow (ExtensionCategory.waldhausenStructure V)
            i.succ j.succ k.succ hij hjk).obj ((cutArrowRows N n).obj Y)).obj.hom.hom.left := by
          change IsIso (Y.obj.obj.map (𝟙 (interval (0 : Fin (n.len+1)).succ (0 : Fin
            (n.len+1)).succ le_rfl)))
          infer_instance
        apply ExtensionCategory.cof_cube_of_horizontal_left_isIso V
        · exact cutArrowRows_map_app_cof N f hf (interval i.succ j.succ hij)
        · exact hf i.succ j.succ k.succ hij hjk

end CategoryTheory.Waldhausen.Fibration.RelativeRows
