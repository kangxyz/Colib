/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Reindex
public import Colib.CategoryTheory.Waldhausen.Fibration.WeakEquivalenceCofiber

/-! # Actual relative quotient rows as coarse-weak cofibration chains

The original quotient squares detect the coarse weakness of every initial
filtration arrow. The only additional hypothesis is the structural extension
axiom on actual cofiber squares. No quotient choices are forgotten through an
assumed categorical or homotopical equivalence.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/WeakChains.lean`
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
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- Replace only the actual zero corner of the original quotient square. -/
theorem horizontal_cofiber_isPushout {n : SimplexCategory} (F : QuotientRows.Obj V n)
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      (F.obj.map (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl,hjk⟩)))
      (N.coarse.isZero.from_ (F.obj.obj (interval i j hij)))
      (F.obj.map (homOfLE (show interval i k (hij.trans hjk) ≤ interval j k hjk from ⟨hij,le_rfl⟩)))
      (N.coarse.isZero.to_ (F.obj.obj (interval j k hjk))) := by
  apply (F.property.quotient i j k hij hjk).of_iso (Iso.refl _) (Iso.refl _)
    ((F.property.zero j).iso N.coarse.isZero) (Iso.refl _)
  · simp
  · exact N.coarse.isZero.eq_of_tgt _ _
  · simp
  · exact (F.property.zero j).eq_of_src _ _

/-- The original displayed interval quotient detects the actual horizontal weak map. -/
theorem horizontal_weak_iff_acyclic (he : ExtensionAxiom N.coarse)
    {n : SimplexCategory} (F : QuotientRows.Obj V n)
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    N.coarse.weq
      (F.obj.map (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from
        ⟨le_rfl,hjk⟩))) ↔
      Acyclic N.coarse (F.obj.obj (interval j k hjk)) :=
  weak_iff_acyclic_of_isPushout N.coarse he
    (by rw [N.cof_eq]; exact F.property.cofibration i j k hij hjk)
    (horizontal_cofiber_isPushout N F i j k hij hjk)

/-- The original nonzero initial intervals, with no choice of quotient replacement. -/
def initialFiltrationIndex (n : SimplexCategory) : Fin (n.len + 1) ⥤ Interval (addInitial.obj n) :=
  (show Monotone (fun i : Fin (n.len + 1) ↦ interval 0 i.succ (Fin.zero_le _)) from
    fun _ _ h ↦ ⟨le_rfl, Nat.succ_le_succ h⟩).functor

/-- The actual initial filtration of a one-longer quotient row. -/
def initialFiltration {n : SimplexCategory} (F : QuotientRows.Obj V (addInitial.obj n)) :
    Fin (n.len + 1) ⥤ C := initialFiltrationIndex n ⋙ F.obj

@[simp] theorem initialFiltration_obj {n : SimplexCategory}
    (F : QuotientRows.Obj V (addInitial.obj n)) (i : Fin (n.len + 1)) :
    (initialFiltration F).obj i = F.obj.obj (interval 0 i.succ (Fin.zero_le _)) := rfl

/-- Every original filtration arrow is an actual fine cofibration. -/
theorem initialFiltration_map_cof {n : SimplexCategory}
    (F : QuotientRows.Obj V (addInitial.obj n)) {i j : Fin (n.len + 1)} (f : i ⟶ j) :
    V.cof ((initialFiltration F).map f) :=
  F.property.cofibration 0 i.succ j.succ (Fin.zero_le _) (Nat.succ_le_succ (leOfHom f))

/-- Tail acyclicity is exactly coarse weakness of the original initial filtration. -/
theorem objects_iff_initialFiltration_weak (he : ExtensionAxiom N.coarse)
    {n : SimplexCategory} (F : QuotientRows.Obj V (addInitial.obj n)) :
    objects N n F ↔ ∀ (i j : Fin (n.len + 1)) (f : i ⟶ j),
      N.coarse.weq ((initialFiltration F).map f) := by
  constructor
  · intro h i j f
    exact (horizontal_weak_iff_acyclic N he F 0 i.succ j.succ
      (Fin.zero_le _) (Nat.succ_le_succ (leOfHom f))).2 (h (interval i j (leOfHom f)))
  · intro h p
    rcases p with ⟨⟨i,j⟩, hij⟩
    exact (horizontal_weak_iff_acyclic N he F 0 i.succ j.succ
      (Fin.zero_le _) (Nat.succ_le_succ hij)).1 (h i j (homOfLE hij))

/-- In every genuine relative row all original filtration maps are coarse-weak. -/
theorem initialFiltration_map_weak (he : ExtensionAxiom N.coarse)
    {n : SimplexCategory} (F : Obj N n) {i j : Fin (n.len + 1)} (f : i ⟶ j) :
    N.coarse.weq ((initialFiltration F.obj).map f) :=
  (objects_iff_initialFiltration_weak N he F.obj).1 F.property i j f

/-- Every original outer restriction retains the literal original filtration. -/
theorem initialFiltration_reindex {m n : SimplexCategory} (α : m ⟶ n) (F : Obj N n) :
    initialFiltration ((reindex N α).obj F).obj =
      (SimplexCategory.toCat.map α).toFunctor ⋙ initialFiltration F.obj := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
