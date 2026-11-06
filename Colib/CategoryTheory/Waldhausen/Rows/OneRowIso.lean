/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.OneRow

/-! # Original one-step rows and the actual middle-object evaluation

The two diagonal objects are actual zero objects. Their unique zero
isomorphisms, together with the identity on the original middle object,
give a genuine natural isomorphism from the canonical one-step row.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/OneRowIso.lean`
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
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The original sole nondegenerate interval evaluation. -/
def oneEvaluation : Obj W ⦋1⦌ ⥤ C := evaluation W (interval 0 1 (by decide))

/-- The actual zero/identity/zero component isomorphisms. -/
def oneRowIsoAt (F : Obj W ⦋1⦌) (p : Interval ⦋1⦌) :
    ((oneEmbedding W).obj ((oneEvaluation W).obj F)).obj.obj p ≅ F.obj.obj p := by
  rcases p with ⟨⟨i,j⟩, hij⟩
  change Fin 2 at i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact W.isZero.iso (F.property.zero 0)
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Iso.refl _
  | succ i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases j using Fin.cases with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hij)
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact W.isZero.iso (F.property.zero 1)

/-- The original interval maps commute with those actual component isomorphisms. -/
theorem oneRowIsoAt_naturality (F : Obj W ⦋1⦌) {p q : Interval ⦋1⦌} (f : p ⟶ q) :
    ((oneEmbedding W).obj ((oneEvaluation W).obj F)).obj.map f ≫ (oneRowIsoAt W F q).hom =
      (oneRowIsoAt W F p).hom ≫ F.obj.map f := by
  rcases p with ⟨⟨i,j⟩, hij⟩
  rcases q with ⟨⟨k,l⟩, hkl⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> solve
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact False.elim (Nat.not_succ_le_zero 0 hkl)
  | exact W.isZero.eq_of_src _ _
  | exact (F.property.zero 0).eq_of_tgt _ _
  | exact (F.property.zero 1).eq_of_tgt _ _
  | have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp

/-- Every actual one-step quotient row is canonically identified with its original object. -/
def oneRowIso (F : Obj W ⦋1⦌) : (oneEmbedding W).obj ((oneEvaluation W).obj F) ≅ F :=
  (objects W ⦋1⦌).isoMk (NatIso.ofComponents (oneRowIsoAt W F) (oneRowIsoAt_naturality W F))

/-- The one-step reconstruction isomorphism retains every original natural transformation. -/
def oneRoundTripIso : oneEvaluation W ⋙ oneEmbedding W ≅ 𝟭 (Obj W ⦋1⦌) :=
  NatIso.ofComponents (oneRowIso W) (by
    intro F G f
    apply ObjectProperty.hom_ext
    ext p
    rcases p with ⟨⟨i,j⟩, hij⟩
    fin_cases i <;> fin_cases j <;> solve
    | exact False.elim (Nat.not_succ_le_zero 0 hij)
    | exact W.isZero.eq_of_src _ _
    | change f.hom.app (interval 0 1 (by decide)) ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.app (interval 0 1 (by decide))
      simp)

/-- The opposite composite is strictly the original identity functor. -/
@[simp] theorem oneEmbedding_oneEvaluation : oneEmbedding W ⋙ oneEvaluation W = 𝟭 C := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.QuotientRows
