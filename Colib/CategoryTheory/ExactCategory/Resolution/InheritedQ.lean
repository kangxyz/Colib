/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.FullQ
public import Colib.CategoryTheory.ExactCategory.Subcategory

/-! Adapted from `Quillen/Resolution/InheritedQ.lean`.
Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd;
Aglib 2c34f185fa859e862661f939cd216b07bcccfb26.
Actual maps, universal properties, assumptions and universes retained. -/

/-!
# The inherited Q-construction and the full ambient Q-subcategory

The two categories are not identified. Their comparison is proved using
actual admissible subobjects and the factorization of Q-spans.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The actual inherited exact inclusion. -/
abbrev exactInclusion := ExactSubcategory.exactInclusion E P

/-- The actual Q-inclusion factors through the full ambient Q-subcategory. -/
def inheritedToFullQ : (ExactSubcategory.exactStructure E P).QCategory ⥤ FullQ E P where
  obj X := ⟨(exactInclusion E P).mapQ.obj X, X.obj.of.property⟩
  map f := ObjectProperty.homMk ((exactInclusion E P).mapQ.map f)
  map_id X := (qProperty E P).hom_ext ((exactInclusion E P).mapQ.map_id X)
  map_comp f g := (qProperty E P).hom_ext ((exactInclusion E P).mapQ.map_comp f g)

@[simp] theorem inheritedToFullQ_comp :
    inheritedToFullQ E P ⋙ fullQInclusion E P = (exactInclusion E P).mapQ := rfl

/-- The comparison remains faithful, although it generally is not full. -/
instance inheritedToFullQ_faithful : (inheritedToFullQ E P).Faithful where
  map_injective := by
    rintro X Y ⟨s⟩ ⟨t⟩ h
    have h' := congrArg (fun f => f.hom) h
    change QConstruction.mkHom _ _ ((exactInclusion E P).toQCompatibleFunctor.mapSpan s) =
      QConstruction.mkHom _ _ ((exactInclusion E P).toQCompatibleFunctor.mapSpan t) at h'
    obtain ⟨e, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 h'
    exact QConstruction.mkHom_eq_of_apexIso _ _ s t (P.isoMk e) (P.hom_ext hl) (P.hom_ext hr)

/-- An ambient admissible subobject of `B` whose domain lies in the resolving
subcategory. Its morphisms must be admissible in the inherited exact structure. -/
structure AdmissibleSubobject (B : C) where
  /-- The source object in the resolving full subcategory `P`. -/
  obj : P.FullSubcategory
  /-- The underlying admissible monomorphism from the source object into `B`. -/
  hom : obj.obj ⟶ B
  admissible : E.inflation hom

namespace AdmissibleSubobject
variable {E P} {B : C}

/-- A morphism between admissible subobjects of `B`, given by an inflation in the inherited
exact structure whose underlying triangle over `B` commutes. -/
@[ext] structure Hom (X Y : AdmissibleSubobject E P B) where
  /-- The comparison morphism in `P.FullSubcategory`; its underlying map composes with `Y.hom`
  to give `X.hom`. -/
  hom : X.obj ⟶ Y.obj
  admissible : (ExactSubcategory.exactStructure E P).inflation hom
  w : hom.hom ≫ Y.hom = X.hom

instance : Category (AdmissibleSubobject E P B) where
  Hom := Hom
  id X := ⟨𝟙 X.obj, (ExactSubcategory.exactStructure E P).inflation_id _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom,
    (ExactSubcategory.exactStructure E P).inflation_comp _ _ f.admissible g.admissible,
    by rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, g.w, f.w]⟩
  id_comp _ := Hom.ext (by simp)
  comp_id _ := Hom.ext (by simp)
  assoc _ _ _ := Hom.ext (by simp [Category.assoc])

/-- Any two maps of subobjects have the same ordinary ambient morphism. -/
instance homSubsingleton (X Y : AdmissibleSubobject E P B) : Subsingleton (X ⟶ Y) := by
  refine ⟨fun f g => ?_⟩
  apply Hom.ext
  apply P.hom_ext
  let : Mono Y.hom := E.mono_of_inflation Y.admissible
  exact (cancel_mono Y.hom).1 (f.w.trans g.w.symm)

/-- The zero subobject. -/
def zero (B : C) : AdmissibleSubobject E P B where
  obj := ⟨0, P.prop_zero⟩
  hom := 0
  admissible := E.inflation_zero B

/-- Zero is genuinely initial in the category of admissible subobjects. -/
def zeroIsInitial (B : C) : IsInitial (zero (E := E) (P := P) B) := by
  refine IsInitial.ofUniqueHom (fun X => ?_) (fun X f => Subsingleton.elim _ _)
  refine ⟨0, ?_, by simp [zero]⟩
  apply (ExactSubcategory.inflation_iff E P _).2
  refine ⟨X.obj.obj, X.obj.property, 𝟙 _, by simp, ?_⟩
  exact E.conflation_of_deflation_of_isKernel (E.deflation_id _)
    (kernel.isLimitConeZeroCone (𝟙 X.obj.obj))

end AdmissibleSubobject

/-- The inherited-Q costructured comma over a resolving object. -/
abbrev InheritedComma (B : FullQ E P) := CostructuredArrow (inheritedToFullQ E P) B

/-- An ordinary admissible subobject determines its forward Q-arrow. -/
@[implicit_reducible]
def subobjectsToComma (B : FullQ E P) :
    AdmissibleSubobject E P B.obj.obj.of ⥤ InheritedComma E P B where
  obj X := CostructuredArrow.mk
    (Y := QConstruction.of _ _ X.obj) (ObjectProperty.homMk (E.qInflation X.hom X.admissible))
  map {X Y} f := CostructuredArrow.homMk
    ((ExactSubcategory.exactStructure E P).qInflation f.hom f.admissible) (by
      apply ObjectProperty.hom_ext
      change (exactInclusion E P).mapQ.map
        ((ExactSubcategory.exactStructure E P).qInflation f.hom f.admissible) ≫
          E.qInflation Y.hom Y.admissible = E.qInflation X.hom X.admissible
      rw [CategoryTheory.ExactCategory.ExactFunctor.mapQ_qInflation, E.qInflation_comp]
      simp only [ExactSubcategory.exactInclusion, ObjectProperty.ι_map, f.w])
  map_id X := by
    apply CostructuredArrow.hom_ext
    exact (ExactSubcategory.exactStructure E P).qInflation_id X.obj
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact ((ExactSubcategory.exactStructure E P).qInflation_comp _ _ _ _).symm

variable [E.IsAdmissibleSubobjectClosed P]

/-- Deflations between resolving objects are admissible in the inherited
structure because their actual kernel is an admissible subobject. -/
lemma inherited_deflation {X Y : P.FullSubcategory} (p : X.obj ⟶ Y.obj)
    (hp : E.deflation p) : (ExactSubcategory.exactStructure E P).deflation (P.homMk p) := by
  obtain ⟨K, i, hi, hS⟩ := hp
  apply (ExactSubcategory.deflation_iff E P _).2
  exact ⟨K, E.prop_of_inflation P i (E.inflation_of_conflation hS) X.property,
    i, hi, hS⟩

/-- The apex of an ambient span is the corresponding ordinary subobject. -/
@[implicit_reducible]
def spanSubobject (B : FullQ E P) (A : InheritedComma E P B)
    (s : Span E.deflation E.inflation A.left.obj.of.obj B.obj.obj.of) :
    AdmissibleSubobject E P B.obj.obj.of where
  obj := ⟨s.apex, E.prop_of_inflation P s.r s.wr B.property⟩
  hom := s.r
  admissible := s.wr

/-- The reversed left leg is an actual arrow in the inherited Q-category. -/
@[implicit_reducible]
def spanUnit (B : FullQ E P) (A : InheritedComma E P B)
    (s : Span E.deflation E.inflation A.left.obj.of.obj B.obj.obj.of)
    (hs : QConstruction.mkHom _ _ s = A.hom.hom) :
    A ⟶ (subobjectsToComma E P B).obj (spanSubobject E P B A s) :=
  CostructuredArrow.homMk
    ((ExactSubcategory.exactStructure E P).qDeflation (P.homMk s.l)
      (inherited_deflation E P
        (X := (spanSubobject E P B A s).obj) (Y := A.left.obj.of) s.l s.wl)) (by
        apply ObjectProperty.hom_ext
        change (exactInclusion E P).mapQ.map
          ((ExactSubcategory.exactStructure E P).qDeflation
            (P.homMk s.l : (spanSubobject E P B A s).obj ⟶ A.left.obj.of) _) ≫
          E.qInflation s.r s.wr = A.hom.hom
        rw [CategoryTheory.ExactCategory.ExactFunctor.mapQ_qDeflation]
        exact (E.qSpan_factor s).symm.trans hs)

/-- The proposed universal reflection arrow into ordinary subobjects. -/
@[implicit_reducible]
def subobjectUniversal (B : FullQ E P) (A : InheritedComma E P B)
    (s : Span E.deflation E.inflation A.left.obj.of.obj B.obj.obj.of)
    (hs : QConstruction.mkHom _ _ s = A.hom.hom) :
    StructuredArrow A (subobjectsToComma E P B) :=
  StructuredArrow.mk (Y := spanSubobject E P B A s) (spanUnit E P B A s hs)

/-- The representative of a comma arrow factors uniquely through the apex of
the source span, with an admissible right leg in the inherited exact category. -/
theorem subobjectUniversal_nonempty_hom (B : FullQ E P) (A : InheritedComma E P B)
    (s : Span E.deflation E.inflation A.left.obj.of.obj B.obj.obj.of)
    (hs : QConstruction.mkHom _ _ s = A.hom.hom)
    (V : StructuredArrow A (subobjectsToComma E P B)) :
    Nonempty (subobjectUniversal E P B A s hs ⟶ V) := by
  obtain ⟨t, ht⟩ := Quotient.exists_rep V.hom.left
  change Span (ExactSubcategory.exactStructure E P).deflation
    (ExactSubcategory.exactStructure E P).inflation A.left.obj.of V.right.obj at t
  change QConstruction.mkHom _ _ t = V.hom.left at ht
  have hw := congrArg (fun k => k.hom) (CostructuredArrow.w V.hom)
  change (exactInclusion E P).mapQ.map V.hom.left ≫ E.qInflation V.right.hom V.right.admissible =
    A.hom.hom at hw
  rw [← ht] at hw
  change QConstruction.mkHom _ _ ((exactInclusion E P).toQCompatibleFunctor.mapSpan t) ≫
    E.qInflation V.right.hom V.right.admissible = A.hom.hom at hw
  rw [E.qSpan_comp_inflation, ← hs] at hw
  obtain ⟨e, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 hw
  change t.apex.obj ≅ s.apex at e
  change e.hom ≫ s.l = t.l.hom at hl
  change e.hom ≫ s.r = t.r.hom ≫ V.right.hom at hr
  let ep : t.apex ≅ (spanSubobject E P B A s).obj := P.isoMk e
  let f : spanSubobject E P B A s ⟶ V.right :=
    { hom := ep.inv ≫ t.r
      admissible := (ExactSubcategory.exactStructure E P).inflation_comp _ _
        ((ExactSubcategory.exactStructure E P).inflation_of_iso ep.symm) t.wr
      w := by
        change (e.inv ≫ t.r.hom) ≫ V.right.hom = s.r
        simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
          congrArg (fun k => e.inv ≫ k) hr.symm }
  refine ⟨StructuredArrow.homMk f ?_⟩
  apply CostructuredArrow.hom_ext
  change (ExactSubcategory.exactStructure E P).qDeflation
    (P.homMk s.l : (spanSubobject E P B A s).obj ⟶ A.left.obj.of) _ ≫
    (ExactSubcategory.exactStructure E P).qInflation f.hom f.admissible = V.hom.left
  rw [← ht]
  refine ((ExactSubcategory.exactStructure E P).qSpan_factor
    (⟨(spanSubobject E P B A s).obj, P.homMk s.l, f.hom,
      inherited_deflation E P (X := (spanSubobject E P B A s).obj)
        (Y := A.left.obj.of) s.l s.wl, f.admissible⟩ :
      Span (ExactSubcategory.exactStructure E P).deflation
        (ExactSubcategory.exactStructure E P).inflation A.left.obj.of V.right.obj)).symm.trans ?_
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ t ep.symm
  · apply P.hom_ext
    exact (Iso.inv_comp_eq e).2 hl.symm
  · rfl

/-- The target subobject category is thin, hence the factorization is unique. -/
def subobjectUniversalIsInitial (B : FullQ E P) (A : InheritedComma E P B)
    (s : Span E.deflation E.inflation A.left.obj.of.obj B.obj.obj.of)
    (hs : QConstruction.mkHom _ _ s = A.hom.hom) :
    IsInitial (subobjectUniversal E P B A s hs) :=
  IsInitial.ofUniqueHom
    (fun V => Classical.choice (subobjectUniversal_nonempty_hom E P B A s hs V))
    (fun _ _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))

instance subobjectsToComma_hasInitials (B : FullQ E P) (A : InheritedComma E P B) :
    HasInitial (StructuredArrow A (subobjectsToComma E P B)) := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep A.hom.hom
  exact (subobjectUniversalIsInitial E P B A s hs).hasInitial

/-- A genuine reflection onto ordinary admissible subobjects. -/
def subobjectAdjunction (B : FullQ E P) :
    leftAdjointOfStructuredArrowInitials (subobjectsToComma E P B) ⊣
      subobjectsToComma E P B := adjunctionOfStructuredArrowInitials _

end CategoryTheory.ExactCategory.Resolution
