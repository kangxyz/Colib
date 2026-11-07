/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Index
public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory

/-! # The actual relative quotient-row Waldhausen categories

An object is an original one-longer quotient row whose original tail
quotients are coarse-acyclic. The fine weak class is retained. Pushout
closure is proved from the actual component pushouts and coarse gluing.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/Structure.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The original one-longer row has genuinely coarse-acyclic tail quotient objects. -/
def objects (n : SimplexCategory) : ObjectProperty (QuotientRows.Obj V (addInitial.obj n)) :=
  fun F ↦ ∀ p : Interval n, Acyclic N.coarse (F.obj.obj ((QuotientRows.indexMap (tail.app
    n)).obj p))
/-- The full category of one-longer quotient rows whose tail quotient objects are
coarse-acyclic. -/
abbrev Obj (n : SimplexCategory) := (objects N n).FullSubcategory

/-- The inclusion of relative rows into the category of one-longer quotient rows, forgetting
only coarse acyclicity of the tail quotients. -/
def forget (n : SimplexCategory) : Obj N n ⥤ QuotientRows.Obj V (addInitial.obj n) := (objects N
    n).ι
instance forget_full (n) : (forget N n).Full := by unfold forget; infer_instance
instance forget_faithful (n) : (forget N n).Faithful := by unfold forget; infer_instance

/-- The cofibration class on relative rows inherited from the one-longer quotient-row Waldhausen
structure. -/
def cof (n : SimplexCategory) : MorphismProperty (Obj N n) :=
  (QuotientRows.waldhausenStructure V (addInitial.obj n)).cof.inverseImage (forget N n)
/-- The fine weak-equivalence class on relative rows inherited from the one-longer quotient-row
Waldhausen structure. -/
def weq (n : SimplexCategory) : MorphismProperty (Obj N n) :=
  (QuotientRows.waldhausenStructure V (addInitial.obj n)).weq.inverseImage (forget N n)
instance cof_multiplicative (n) : (cof N n).IsMultiplicative := by unfold cof; infer_instance
instance weq_multiplicative (n) : (weq N n).IsMultiplicative := by unfold weq; infer_instance

/-- The inherited chosen zero is literally the original constant zero row. -/
def zero (n : SimplexCategory) : Obj N n :=
  ⟨QuotientRows.zero V (addInitial.obj n), fun _ ↦ acyclic_of_isZero N.coarse V.isZero⟩

theorem isZero (n : SimplexCategory) : IsZero (zero N n) :=
  IsZero.of_full_of_faithful_of_isZero (forget N n) (zero N n) (QuotientRows.isZero V
    (addInitial.obj n))

/-- Construct an actual inherited pushout, retaining its original ambient-row square. -/
theorem exists_pushout {n : SimplexCategory} {A B D : Obj N n}
    (f : A ⟶ B) (g : A ⟶ D) (hf : cof N n f) :
    ∃ (P : Obj N n) (i : B ⟶ P) (j : D ⟶ P), IsPushout f g i j ∧ IsPushout f.hom g.hom i.hom
      j.hom := by
  obtain ⟨P, i, j, h⟩ := (QuotientRows.waldhausenStructure V (addInitial.obj n)).pushout_exists
    f.hom g.hom hf
  have hP : objects N n P := by
    intro p
    exact acyclic_of_isPushout N.coarse
      (by rw [N.cof_eq]; exact QuotientRows.cof_app V hf _)
      (QuotientRows.pointwise_of_isPushout V hf h ((QuotientRows.indexMap (tail.app n)).obj p))
      (A.property p) (B.property p) (D.property p)
  let P' : Obj N n := ⟨P, hP⟩
  let i' : B ⟶ P' := (objects N n).homMk i
  let j' : D ⟶ P' := (objects N n).homMk j
  exact ⟨P', i', j', IsPushout.of_map_of_faithful (forget N n) h, h⟩

/-- Every displayed inherited pushout along a genuine cofibration is an actual ambient-row
pushout. -/
theorem forget_map_pushout {n : SimplexCategory} {A B D P : Obj N n}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
    (hf : cof N n f) (h : IsPushout f g i j) : IsPushout f.hom g.hom i.hom j.hom := by
  obtain ⟨P₀, i₀, j₀, h₀, hamb⟩ := exists_pushout N f g hf
  let e : P₀ ≅ P := h₀.isoIsPushout _ _ h
  apply hamb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ((forget N n).mapIso e)
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp] using!
      congrArg (fun k ↦ k.hom) (h₀.inl_isoIsPushout_hom _ _ h)
  · simpa only [Iso.refl_hom, Category.id_comp] using!
      congrArg (fun k ↦ k.hom) (h₀.inr_isoIsPushout_hom _ _ h)

/-- The actual relative rows carry the inherited fine Waldhausen structure. -/
def waldhausenStructure (n : SimplexCategory) : Structure (Obj N n) where
  zero := zero N n
  isZero := isZero N n
  cof := cof N n
  weq := weq N n
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact (QuotientRows.waldhausenStructure V (addInitial.obj n)).cof_iso _
      (inferInstance : IsIso ((forget N n).map f))
  weq_iso := by
    intro A B f hf
    let : IsIso f := hf
    exact (QuotientRows.waldhausenStructure V (addInitial.obj n)).weq_iso _
      (inferInstance : IsIso ((forget N n).map f))
  cof_zero F := by
    have h : ((isZero N n).to_ F).hom = (QuotientRows.isZero V (addInitial.obj n)).to_ F.obj :=
      (QuotientRows.isZero V (addInitial.obj n)).eq_of_src _ _
    change QuotientRows.cof V (addInitial.obj n) ((isZero N n).to_ F).hom
    rw [h]
    exact QuotientRows.cof_zero V (addInitial.obj n) F.obj
  pushout_exists f g hf := by
    obtain ⟨P, i, j, h, _⟩ := exists_pushout N f g hf
    exact ⟨P, i, j, h⟩
  cof_pushout hf h := (QuotientRows.waldhausenStructure V (addInitial.obj n)).cof_pushout hf
    (forget_map_pushout N hf h)
  gluing := by
    intro A B D P A' B' D' P' f g i j f' g' i' j' a b d p hf hf' h h' ef eg ei ej ha hb hd
    exact (QuotientRows.waldhausenStructure V (addInitial.obj n)).gluing a.hom b.hom d.hom p.hom
      hf hf' (forget_map_pushout N hf h) (forget_map_pushout N hf' h')
      (congrArg (fun k ↦ k.hom) ef) (congrArg (fun k ↦ k.hom) eg)
      (congrArg (fun k ↦ k.hom) ei) (congrArg (fun k ↦ k.hom) ej) ha hb hd

/-- The literal inclusion into original one-longer quotient rows is genuinely exact. -/
theorem forget_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
      (QuotientRows.waldhausenStructure V (addInitial.obj n)).cof
      (QuotientRows.waldhausenStructure V (addInitial.obj n)).weq (forget N n) where
  zero h := (QuotientRows.isZero V (addInitial.obj n)).of_iso ((forget N n).mapIso (h.iso
    (isZero N n)))
  cofibration _ h := h
  weak _ h := h
  pushout hf h := forget_map_pushout N hf h

/-- The first relative object. This evaluation is degreewise; it is not asserted to be
outer-simplicial. -/
def first (n : SimplexCategory) : Obj N n ⥤ C :=
  forget N n ⋙ QuotientRows.evaluation V (firstInterval n)

theorem first_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq V.cof V.weq (first N n) :=
  (forget_exact N n).comp (QuotientRows.evaluation_exact V (firstInterval n))

/-- The original ambient tail row, before lifting its proved acyclic objects. -/
def tailUnderlying (n : SimplexCategory) : Obj N n ⥤ QuotientRows.Obj V n :=
  forget N n ⋙ QuotientRows.reindex V (tail.app n)

theorem tailUnderlying_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
      (QuotientRows.waldhausenStructure V n).cof (QuotientRows.waldhausenStructure V n).weq
      (tailUnderlying N n) :=
  (forget_exact N n).comp (QuotientRows.reindex_exact V (tail.app n))

end CategoryTheory.Waldhausen.Fibration.RelativeRows
