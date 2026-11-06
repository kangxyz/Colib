/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Reindex
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.NestedWeakEquivalences
public import Colib.CategoryTheory.Waldhausen.Rows.Interchange
public import Colib.CategoryTheory.Waldhausen.Rows.PostcomposeDetection

/-! # Actual interchange of relative rows and an inner S-construction

The equivalence keeps the original two interval coordinates. Tail acyclicity
is detected on the actual inner-row components. No cylinder, extension axiom,
or weak-equivalence saturation is needed for this structural interchange.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/Interchange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C]

/-- Acyclicity can be tested with the actual map out of any genuine zero object. -/
theorem acyclic_iff_weak_from_isZero (W : Structure C) {Z : C} (hZ : IsZero Z) (X : C) :
    Acyclic W X ↔ W.weq (hZ.to_ X) := by
  constructor
  · intro h
    have e : hZ.to_ X = (hZ.iso W.isZero).hom ≫ W.isZero.to_ X := hZ.eq_of_src _ _
    rw [e]
    exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance) h
  · intro h
    have e : W.isZero.to_ X = (W.isZero.iso hZ).hom ≫ hZ.to_ X := W.isZero.eq_of_src _ _
    change W.weq _
    rw [e]
    exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance) h

variable {V : Structure C} (N : NestedWeakEquivalences V)

/-- Acyclicity of the original coarse row is exactly original component acyclicity. -/
theorem rowAcyclic_iff {m : SimplexCategory} (X : QuotientRows.Obj V m) :
    Acyclic (RowWeakEquivalences.coarseStructure N m) X ↔
      ∀ p, Acyclic N.coarse (X.obj.obj p) := by
  change (∀ p, N.coarse.weq (((QuotientRows.isZero V m).to_ X).hom.app p)) ↔ _
  have hp (p : Interval m) : ((QuotientRows.isZero V m).to_ X).hom.app p =
      V.isZero.to_ (X.obj.obj p) := V.isZero.eq_of_src _ _
  simp_rw [hp, ← acyclic_iff_weak_from_isZero N.coarse V.isZero]

namespace RelativeRows

/-- Forget only the relative condition, then transpose the genuine quotient rows. -/
def innerSUnderlying (m n : SimplexCategory) :
    QuotientRows.Obj (waldhausenStructure N n) m ⥤
      QuotientRows.Obj (QuotientRows.waldhausenStructure V m) (addInitial.obj n) :=
  QuotientRows.postcompose (waldhausenStructure N n)
    (QuotientRows.waldhausenStructure V (addInitial.obj n)) (forget_exact N n) m ⋙
      QuotientRows.transposeRows V m (addInitial.obj n)

/-- The unchanged transposed tail is genuinely coarse-acyclic as an inner row. -/
theorem innerSUnderlying_relative (m n : SimplexCategory)
    (X : QuotientRows.Obj (waldhausenStructure N n) m) :
    objects (RowWeakEquivalences.nested N m) n ((innerSUnderlying N m n).obj X) := by
  intro p
  apply (rowAcyclic_iff N _).2
  intro q
  exact (X.obj.obj q).property p

/-- The literal forward interchange on actual relative quotient rows. -/
def innerSInterchange (m n : SimplexCategory) :
    QuotientRows.Obj (waldhausenStructure N n) m ⥤ Obj (RowWeakEquivalences.nested N m) n :=
  (objects (RowWeakEquivalences.nested N m) n).lift (innerSUnderlying N m n)
    (innerSUnderlying_relative N m n)

/-- The inverse component diagram, keeping all original interval coordinates. -/
def innerSInverseDiagram {m n : SimplexCategory} (X : Obj (RowWeakEquivalences.nested N m) n) :
    Interval m ⥤ Obj N n where
  obj q := ⟨((QuotientRows.transposeRows V (addInitial.obj n) m).obj X.obj).obj.obj q,
    fun p ↦ (rowAcyclic_iff N _).1 (X.property p) q⟩
  map f := (objects N n).homMk
    (((QuotientRows.transposeRows V (addInitial.obj n) m).obj X.obj).obj.map f)
  map_id q := by
    apply ObjectProperty.hom_ext
    exact ((QuotientRows.transposeRows V (addInitial.obj n) m).obj X.obj).obj.map_id q
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact ((QuotientRows.transposeRows V (addInitial.obj n) m).obj X.obj).obj.map_comp f g

/-- The inherited relative-row conditions are reflected by the original full inclusion. -/
theorem innerSInverseDiagram_isRow {m n : SimplexCategory}
    (X : Obj (RowWeakEquivalences.nested N m) n) :
    QuotientRows.IsRow (waldhausenStructure N n) (innerSInverseDiagram N X) where
  zero i := IsZero.of_full_of_faithful_of_isZero (forget N n) _
    (((QuotientRows.transposeRows V (addInitial.obj n) m).obj X.obj).property.zero i)
  cofibration i j k hij hjk :=
    ((QuotientRows.transposeRows V (addInitial.obj n) m).obj X.obj).property.cofibration i j k
      hij hjk
  quotient i j k hij hjk := IsPushout.of_map_of_faithful (forget N n)
    (((QuotientRows.transposeRows V (addInitial.obj n) m).obj X.obj).property.quotient i j k hij
      hjk)

/-- Genuine inverse interchange into the S-construction of the original relative category. -/
def innerSInverse (m n : SimplexCategory) :
    Obj (RowWeakEquivalences.nested N m) n ⥤ QuotientRows.Obj (waldhausenStructure N n) m where
  obj X := ⟨innerSInverseDiagram N X, innerSInverseDiagram_isRow N X⟩
  map f := (QuotientRows.objects (waldhausenStructure N n) m).homMk {
    app q := (objects N n).homMk
      (((QuotientRows.transposeRows V (addInitial.obj n) m).map f.hom).hom.app q)
    naturality q q' a := by
      apply ObjectProperty.hom_ext
      exact ((QuotientRows.transposeRows V (addInitial.obj n) m).map f.hom).hom.naturality a }
  map_id _ := by
    apply ObjectProperty.hom_ext
    ext q p
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    ext q p
    rfl

@[simp] theorem innerSInterchange_inverse (m n : SimplexCategory) :
    innerSInterchange N m n ⋙ innerSInverse N m n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem innerSInverse_interchange (m n : SimplexCategory) :
    innerSInverse N m n ⋙ innerSInterchange N m n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual relative-inner-S interchange is a genuine categorical equivalence. -/
def innerSEquivalence (m n : SimplexCategory) :
    QuotientRows.Obj (waldhausenStructure N n) m ≌ Obj (RowWeakEquivalences.nested N m) n :=
  CategoryTheory.Equivalence.mk (innerSInterchange N m n) (innerSInverse N m n)
    (eqToIso (innerSInterchange_inverse N m n).symm)
    (eqToIso (innerSInverse_interchange N m n))

/-- The original ambient-row forward functor is retained exactly. -/
@[simp] theorem innerSInterchange_forget (m n : SimplexCategory) :
    innerSInterchange N m n ⋙ forget (RowWeakEquivalences.nested N m) n =
      innerSUnderlying N m n := rfl

/-- The inverse ambient row is the original quotient-row transpose. -/
@[simp] theorem innerSInverse_forget (m n : SimplexCategory) :
    innerSInverse N m n ⋙ QuotientRows.postcompose (waldhausenStructure N n)
      (QuotientRows.waldhausenStructure V (addInitial.obj n)) (forget_exact N n) m =
      forget (RowWeakEquivalences.nested N m) n ⋙
        QuotientRows.transposeRows V (addInitial.obj n) m := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Actual fine weak maps are preserved in the original forward direction. -/
theorem innerSInterchange_weak {m n : SimplexCategory}
    {X Y : QuotientRows.Obj (waldhausenStructure N n) m} (f : X ⟶ Y)
    (hf : (QuotientRows.waldhausenStructure (waldhausenStructure N n) m).weq f) :
    (waldhausenStructure (RowWeakEquivalences.nested N m) n).weq ((innerSInterchange N m n).map
      f) :=
  fun p q ↦ hf q p

/-- The actual forward functor preserves the full Reedy cofibration predicate. -/
theorem innerSInterchange_cof {m n : SimplexCategory}
    {X Y : QuotientRows.Obj (waldhausenStructure N n) m} (f : X ⟶ Y)
    (hf : (QuotientRows.waldhausenStructure (waldhausenStructure N n) m).cof f) :
    (waldhausenStructure (RowWeakEquivalences.nested N m) n).cof ((innerSInterchange N m n).map
      f) :=
  QuotientRows.transposeRows_cof V (QuotientRows.postcompose_cof _ _ (forget_exact N n) hf)

/-- Inverse cofibrancy follows by actual reflection through the exact full inclusion. -/
theorem innerSInverse_cof {m n : SimplexCategory}
    {X Y : Obj (RowWeakEquivalences.nested N m) n} (f : X ⟶ Y)
    (hf : (waldhausenStructure (RowWeakEquivalences.nested N m) n).cof f) :
    (QuotientRows.waldhausenStructure (waldhausenStructure N n) m).cof ((innerSInverse N m
      n).map f) := by
  apply QuotientRows.cof_of_postcompose _ _ (forget_exact N n) (fun {_ _} _ h ↦ h)
  exact QuotientRows.transposeRows_cof V hf

/-- Both inherited fine Waldhausen structures are preserved by the original interchange. -/
theorem innerSInterchange_exact (m n : SimplexCategory) :
    IsExact (QuotientRows.waldhausenStructure (waldhausenStructure N n) m).cof
      (QuotientRows.waldhausenStructure (waldhausenStructure N n) m).weq
      (waldhausenStructure (RowWeakEquivalences.nested N m) n).cof
      (waldhausenStructure (RowWeakEquivalences.nested N m) n).weq (innerSInterchange N m n) where
  zero h := (isZero (RowWeakEquivalences.nested N m) n).of_iso
    ((innerSInterchange N m n).mapIso (h.iso (QuotientRows.isZero (waldhausenStructure N n) m)))
  cofibration _ h := innerSInterchange_cof N _ h
  weak _ h := innerSInterchange_weak N _ h
  pushout _ h := by
    let : (innerSInterchange N m n).IsEquivalence := (innerSEquivalence N m n).isEquivalence_functor
    exact h.map (innerSInterchange N m n)

/-- The inverse is genuinely exact; the relative full inclusion detects its Reedy cofibrations. -/
theorem innerSInverse_exact (m n : SimplexCategory) :
    IsExact (waldhausenStructure (RowWeakEquivalences.nested N m) n).cof
      (waldhausenStructure (RowWeakEquivalences.nested N m) n).weq
      (QuotientRows.waldhausenStructure (waldhausenStructure N n) m).cof
      (QuotientRows.waldhausenStructure (waldhausenStructure N n) m).weq (innerSInverse N m n) where
  zero h := (QuotientRows.isZero (waldhausenStructure N n) m).of_iso
    ((innerSInverse N m n).mapIso (h.iso (isZero (RowWeakEquivalences.nested N m) n)))
  cofibration _ h := innerSInverse_cof N _ h
  weak _ h q p := h p q
  pushout _ h := by
    let : (innerSInverse N m n).IsEquivalence := (innerSEquivalence N m n).isEquivalence_inverse
    exact h.map (innerSInverse N m n)

/-- Every original relative ordinal restriction commutes strictly with interchange. -/
theorem innerSInterchange_reindex {m n n' : SimplexCategory} (α : n' ⟶ n) :
    QuotientRows.postcompose (waldhausenStructure N n) (waldhausenStructure N n')
        (reindex_exact N α) m ⋙ innerSInterchange N m n' =
      innerSInterchange N m n ⋙ reindex (RowWeakEquivalences.nested N m) α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end RelativeRows
end CategoryTheory.Waldhausen.Fibration
