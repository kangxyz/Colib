/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.InitialCutExact
public import Colib.CategoryTheory.Waldhausen.Additivity.CofibrationSequence

/-! # The actual tail quotient of the cutoff subrow

The quotient is the original acyclic tail with its first vertex duplicated.
The cofiber square is proved on each original interval using the original
row quotient square, or a square with actual zero-object isomorphisms.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/TailQuotient.lean`
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

/-- Raise the added vertex to the first tail vertex, fixing every tail vertex. -/
def raiseIndex (n : SimplexCategory) : addInitial.obj n ⟶ addInitial.obj n :=
  dropInitial n ≫ tail.app n

theorem le_raiseIndex (n : SimplexCategory) (i : Fin ((addInitial.obj n).len + 1)) :
    i ≤ (raiseIndex n).toOrderHom i := by
  change Fin (n.len + 1 + 1) at i
  cases i using Fin.cases with
  | zero => exact Fin.zero_le _
  | succ _ => exact le_rfl

/-- The original map of each interval to its tail quotient interval. -/
def idToRaiseIndex (n : SimplexCategory) : 𝟭 (Interval (addInitial.obj n)) ⟶
    QuotientRows.indexMap (raiseIndex n) where
  app p := homOfLE ⟨le_raiseIndex n p.val.1, le_raiseIndex n p.val.2⟩
  naturality _ _ _ := Subsingleton.elim _ _

/-- The actual original tail quotient, with its zero first object. -/
def tailQuotientFunctor (n : SimplexCategory) : Obj N n ⥤ Obj N n :=
  tailFunctor N n ⋙ tailSection N n

/-- The original quotient transformation on actual interval maps. -/
def tailProjection (n : SimplexCategory) : 𝟭 (Obj N n) ⟶ tailQuotientFunctor N n where
  app X := (objects N n).homMk ((QuotientRows.objects V (addInitial.obj n)).homMk
    (Functor.whiskerRight (idToRaiseIndex n) X.obj.obj))
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    ext p
    exact (f.hom.hom.naturality ((idToRaiseIndex n).app p)).symm

/-- The actual cofiber square on every original interval, for the unique maps through the chosen
zero. -/
theorem cut_tail_cofiber_component (n : SimplexCategory) (X : Obj N n)
    (p : Interval (addInitial.obj n))
    (g : ((cutFunctor N n).obj X).obj.obj.obj p ⟶ V.zero)
    (j : V.zero ⟶ ((tailQuotientFunctor N n).obj X).obj.obj.obj p) :
    IsPushout (((cutToId N n).app X).hom.hom.app p) g
      (((tailProjection N n).app X).hom.hom.app p) j := by
  rcases p with ⟨⟨i,k⟩, hik⟩
  change Fin (n.len + 1 + 1) at i k
  cases i using Fin.cases with
  | zero =>
    cases k using Fin.cases with
    | zero =>
      have hf : IsIso ((((cutToId N n).app X).hom.hom.app (interval 0 0 hik))) := by
        change IsIso (X.obj.obj.map (𝟙 (interval 0 0 le_rfl)))
        infer_instance
      have hj : IsIso j := V.isZero.isIso (X.obj.property.zero (0 : Fin (n.len+1)).succ) j
      exact @IsPushout.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ hf hj ⟨(X.obj.property.zero
        0).eq_of_src _ _⟩
    | succ k =>
      let e := (X.obj.property.zero (0 : Fin (n.len+1)).succ).iso V.isZero
      apply (X.obj.property.quotient 0 (0 : Fin (n.len+1)).succ k.succ
        (Fin.zero_le _) (Nat.succ_le_succ (Fin.zero_le k))).of_iso
        (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        rfl
      · exact V.isZero.eq_of_tgt _ _
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        rfl
      · exact (X.obj.property.zero (0 : Fin (n.len+1)).succ).eq_of_src _ _
  | succ i =>
    cases k using Fin.cases with
    | zero => have h : i.val + 1 ≤ 0 := hik; omega
    | succ k =>
      have hg : IsIso g := (X.obj.property.zero (0 : Fin (n.len+1)).succ).isIso V.isZero g
      have hh : IsIso ((((tailProjection N n).app X).hom.hom.app (interval i.succ k.succ hik)))
        := by
        change IsIso (X.obj.obj.map (𝟙 (interval i.succ k.succ hik)))
        infer_instance
      exact @IsPushout.of_vert_isIso _ _ _ _ _ _ _ _ _ _ hg hh ⟨(X.obj.property.zero (0 : Fin
        (n.len+1)).succ).eq_of_src _ _⟩

/-- The original relative-row cofiber square is a genuine pushout. -/
theorem cut_tail_cofiber (n : SimplexCategory) (X : Obj N n) :
    IsPushout ((cutToId N n).app X)
      ((isZero N n).from_ ((cutFunctor N n).obj X))
      ((tailProjection N n).app X)
      ((isZero N n).to_ ((tailQuotientFunctor N n).obj X)) := by
  apply IsPushout.of_map_of_faithful (forget N n)
  apply QuotientRows.isPushout_of_pointwise V
  intro p
  exact cut_tail_cofiber_component N n X p _ _

/-- The actual initial-cutoff/identity/tail-quotient sequence is genuinely structural. -/
theorem cut_tail_isCofibrationSequence (n : SimplexCategory) :
    Additivity.IsCofibrationSequence (waldhausenStructure N n) (waldhausenStructure N n)
      (cutToId N n) (tailProjection N n) where
  exactF := cutFunctor_exact N n
  exactG := IsExact.id _ _
  exactH := (tailFunctor_exact N n).comp (tailSection_exact N n)
  cofibration := cutToId_isCofibrationTransformation N n
  cofiber := cut_tail_cofiber N n

end CategoryTheory.Waldhausen.Fibration.RelativeRows
