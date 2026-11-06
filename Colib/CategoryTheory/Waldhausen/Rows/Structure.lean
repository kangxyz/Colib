/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Pushouts

/-! # The genuine Waldhausen structure on actual quotient grids

Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/Structure.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C) {n : SimplexCategory}

/-- A row of actual zero objects is a zero object of the full row category. -/
theorem isZero_of_components (F : Obj W n) (hF : ∀ p, IsZero (F.obj.obj p)) : IsZero F where
  unique_to G := by
    refine ⟨{ default := (objects W n).homMk {
      app p := (hF p).to_ (G.obj.obj p)
      naturality p _ _ := (hF p).eq_of_src _ _ }, uniq := ?_ }⟩
    intro η
    apply ObjectProperty.hom_ext
    ext p
    exact (hF p).eq_of_src _ _
  unique_from G := by
    refine ⟨{ default := (objects W n).homMk {
      app p := (hF p).from_ (G.obj.obj p)
      naturality _ q _ := (hF q).eq_of_tgt _ _ }, uniq := ?_ }⟩
    intro η
    apply ObjectProperty.hom_ext
    ext p
    exact (hF p).eq_of_tgt _ _

/-- Every component of a genuine zero row is zero. -/
theorem evaluation_isZero {F : Obj W n} (hF : IsZero F) (p : Interval n) :
    IsZero ((evaluation W p).obj F) :=
  W.isZero.of_iso ((evaluation W p).mapIso (hF.iso (isZero W n)))

/-- Any displayed pointwise pushout square is a genuine pushout in the full row category. -/
theorem isPushout_of_pointwise {A B D P : Obj W n}
    (f : A ⟶ B) (g : A ⟶ D) (i : B ⟶ P) (j : D ⟶ P)
    (hp : ∀ p, IsPushout (f.hom.app p) (g.hom.app p) (i.hom.app p) (j.hom.app p)) :
    IsPushout f g i j :=
  IsPushout.of_map_of_faithful (forget W n)
    (functor_isPushout_of_pointwise f.hom g.hom i.hom j.hom hp)

/-- The row Waldhausen structure is derived from actual pointwise pushouts
and the all-triples Reedy cofibration condition. -/
def waldhausenStructure (n : SimplexCategory) : Structure (Obj W n) where
  zero := zero W n
  isZero := isZero W n
  cof := cof W n
  weq := weq W n
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := cof_iso W n
  weq_iso := weq_iso W n
  cof_zero := cof_zero W n
  pushout_exists f g hf := by
    obtain ⟨P, i, j, h, _, _⟩ := exists_row_pushout W f g hf
    exact ⟨P, i, j, h⟩
  cof_pushout hf h := cof_of_pointwise_pushout W _ _ _ _ hf (pointwise_of_isPushout W hf h)
  gluing := by
    intro A B D P A' B' D' P' f g i j f' g' i' j' a b d p hf hf' h h' ef eg ei ej ha hb hd q
    exact W.gluing (a.hom.app q) (b.hom.app q) (d.hom.app q) (p.hom.app q)
      (cof_app W hf q) (cof_app W hf' q)
      (pointwise_of_isPushout W hf h q) (pointwise_of_isPushout W hf' h' q)
      (congrArg (fun k ↦ k.hom.app q) ef) (congrArg (fun k ↦ k.hom.app q) eg)
      (congrArg (fun k ↦ k.hom.app q) ei) (congrArg (fun k ↦ k.hom.app q) ej)
      (ha q) (hb q) (hd q)

/-- Evaluation at every original quotient object is genuinely exact. -/
theorem evaluation_exact (p : Interval n) :
    IsExact (waldhausenStructure W n).cof (waldhausenStructure W n).weq W.cof W.weq (evaluation
      W p) where
  zero h := evaluation_isZero W h p
  cofibration _ h := cof_app W h p
  weak _ h := h p
  pushout hf h := pointwise_of_isPushout W hf h p

/-- Restriction to every horizontal interval arrow is genuinely exact into
actual Reedy cofibration arrows. -/
theorem horizontalArrow_exact (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    IsExact (waldhausenStructure W n).cof (waldhausenStructure W n).weq
      (ExtensionCategory.waldhausenStructure W).cof (ExtensionCategory.waldhausenStructure W).weq
      (horizontalArrow W i j k hij hjk) where
  zero h := (ExtensionCategory.isZero W).of_iso
    ((horizontalArrow W i j k hij hjk).mapIso (h.iso (isZero W n)))
  cofibration _ h := h i j k hij hjk
  weak _ h := ⟨h _, h _⟩
  pushout hf h :=
    IsPushout.of_map_of_faithful (ExtensionCategory.forget W)
      (ExtensionCategory.arrow_isPushout _ _ _ _
        (pointwise_of_isPushout W hf h _) (pointwise_of_isPushout W hf h _))

end CategoryTheory.Waldhausen.QuotientRows
