/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Localization.Serre.FiberComparison
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryLift
public import Colib.CategoryTheory.QConstruction.Abelian.ArrowLayers
public import Colib.CategoryTheory.QConstruction.ZeroSource
public import Colib.Topology.ClassifyingSpace.Adjunction
public import Colib.Topology.ClassifyingSpace.Semilattice
public import Colib.CategoryTheory.TheoremA.ContractibleComma

/-! # Comma geometry of a Serre quotient

The target-zero comma category of the actual quotient Q-functor is equivalent
to the Serre Q-category. The source-zero comparison has contractible actual
comma fibers, modeled by semilattices of lifted Serre layers. More generally,
the fibers of the isomorphism-object inclusion into each structured comma
category are equivalent to semilattices of lifted intervals. The proved native
Theorem A gives homotopy equivalences whose forward maps are exactly these
inclusions. No Theorem B transition hypothesis or localization equivalence is
assumed or asserted.

Adapted from `Quillen/Localization/Serre/LocalizationComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native Q-spans,
comma categories, functors and realization maps are retained.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] CategoryTheory.ExactCategory.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The genuine quotient Q-functor carries lower layer endpoints by the
surjective exact subobject map. -/
theorem arrowLower_quotientMapQ {X M : C}
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    QConstruction.arrowLower ((quotientMapQ P).map f) =
      subobjectMap P.isoModSerre.Q P M (QConstruction.arrowLower f) := by
  induction f using Quotient.inductionOn with | _ s =>
  exact (subobjectMap_spanLower P.isoModSerre.Q P s).symm

/-- The quotient Q-functor also carries upper layer endpoints by that map. -/
theorem arrowUpper_quotientMapQ {X M : C}
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    QConstruction.arrowUpper ((quotientMapQ P).map f) =
      subobjectMap P.isoModSerre.Q P M (QConstruction.arrowUpper f) := by
  induction f using Quotient.inductionOn with | _ s =>
  exact (subobjectMap_spanUpper P.isoModSerre.Q P s).symm

/-- The genuine target-zero comma category for the canonical quotient Q-map. -/
abbrev ZeroComma := CostructuredArrow (quotientMapQ P) ((abelianExactStructure
  P.isoModSerre.Localization)).qZero

/-- Every source object occurring in the zero comma category belongs to the
Serre class. This is a consequence of the epi/mono legs of its structure arrow. -/
theorem zeroComma_object_mem (X : ZeroComma P) : P X.left.obj.of :=
  (quotient_isZero_obj_iff P X.left.obj.of).1
    (((abelianExactStructure P.isoModSerre.Localization)).isZero_source_of_qHom X.hom
      (isZero_zero _))

/-- The canonical zero comparison lifts the Q-inclusion to the zero comma
category. The components are exactly the ones used in the localization
nullhomotopy. -/
def serreToZeroComma : (abelianExactStructure P.FullSubcategory).QCategory ⥤
  ZeroComma P :=
  (Abelian.Devissage.mapQ P).toCostructuredArrow (quotientMapQ P) _
    (fun X => (quotientInclusionZeroIso P).hom.app X) (fun f => by
      simpa using (quotientInclusionZeroIso P).hom.naturality f)

/-- Forgetting the structure arrow recovers the actual Q-inclusion strictly. -/
@[simp]
theorem serreToZeroComma_projection :
    serreToZeroComma P ⋙ CostructuredArrow.proj (quotientMapQ P)
      ((abelianExactStructure P.isoModSerre.Localization)).qZero = Abelian.Devissage.mapQ P := rfl

instance serreToZeroComma_faithful : (serreToZeroComma P).Faithful where
  map_injective h := (Abelian.Devissage.mapQ P).map_injective
    (congrArg (fun f => f.left) h)

instance serreToZeroComma_full : (serreToZeroComma P).Full where
  map_surjective f := by
    refine ⟨(Abelian.Devissage.mapQ P).preimage f.left, ?_⟩
    apply CostructuredArrow.hom_ext
    exact (Abelian.Devissage.mapQ P).map_preimage f.left

instance serreToZeroComma_essSurj : (serreToZeroComma P).EssSurj where
  mem_essImage X := by
    let Y : (abelianExactStructure P.FullSubcategory).QCategory :=
      QConstruction.of _ _ ⟨X.left.obj.of, zeroComma_object_mem P X⟩
    refine ⟨Y, ⟨CostructuredArrow.isoMk (Iso.refl _) ?_⟩⟩
    exact (((abelianExactStructure P.isoModSerre.Localization)).qHom_subsingleton_of_isZero _ _
      (isZero_zero _)).elim _ _

/-- The canonical lift of the inclusion is a genuine categorical equivalence. -/
instance serreToZeroComma_isEquivalence : (serreToZeroComma P).IsEquivalence where

/-- The Serre Q-category is equivalent to the actual zero comma category. -/
def zeroCommaEquivalence :
    (abelianExactStructure P.FullSubcategory).QCategory ≌ ZeroComma P :=
  (serreToZeroComma P).asEquivalence

/-- Realization gives a homotopy equivalence with the canonical comparison
as its forward map, not just an abstract equivalence of homotopy types. -/
def zeroCommaClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (abelianExactStructure P.FullSubcategory).KSpace
      (ClassifyingSpace (ZeroComma P)) :=
  equivalenceClassifyingHomotopyEquiv (zeroCommaEquivalence P)

@[simp]
theorem zeroCommaClassifyingHomotopyEquiv_apply
    (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    zeroCommaClassifyingHomotopyEquiv P x = classifyingSpaceMap (serreToZeroComma P) x := rfl

/-- The realized comparison lies strictly over the canonical inclusion map. -/
@[simp]
theorem zeroCommaClassifying_projection :
    (classifyingSpaceMap (CostructuredArrow.proj (quotientMapQ P)
      ((abelianExactStructure P.isoModSerre.Localization)).qZero)).hom.comp
      (classifyingSpaceMap (serreToZeroComma P)).hom =
    (classifyingSpaceMap (Abelian.Devissage.mapQ P)).hom := by
  change (classifyingSpaceMap (serreToZeroComma P) ≫
    classifyingSpaceMap (CostructuredArrow.proj (quotientMapQ P)
      ((abelianExactStructure P.isoModSerre.Localization)).qZero)).hom = _
  rw [← classifyingSpaceMap_comp, serreToZeroComma_projection]

/-- The source-zero comma category used in Quillen's original localization
proof. It is distinct from the target-zero comma category above. -/
abbrev ZeroStructuredComma := StructuredArrow ((abelianExactStructure
  P.isoModSerre.Localization)).qZero (quotientMapQ P)

/-- The Serre inclusion lifted to the structured comma category using the
inverse of the same canonical categorical zero comparison. -/
def serreToZeroStructuredComma :
    (abelianExactStructure P.FullSubcategory).QCategory ⥤ ZeroStructuredComma P :=
  (Abelian.Devissage.mapQ P).toStructuredArrow ((abelianExactStructure
    P.isoModSerre.Localization)).qZero (quotientMapQ P)
    (fun X => (quotientInclusionZeroIso P).inv.app X) (fun f => by
      simpa using ((quotientInclusionZeroIso P).inv.naturality f).symm)

@[simp]
theorem serreToZeroStructuredComma_projection :
    serreToZeroStructuredComma P ⋙ StructuredArrow.proj
      ((abelianExactStructure P.isoModSerre.Localization)).qZero (quotientMapQ P) =
        Abelian.Devissage.mapQ P := rfl

/-- Lift categories of arbitrary quotient intervals admit the same concrete
join contraction, as soon as the specified endpoints are nested. -/
theorem subobjectIntervalLift_contractible (M : C)
    (S T : Subobject (P.isoModSerre.Q.obj M)) (h : S ≤ T) :
    ContractibleSpace (ClassifyingSpace (SubobjectIntervalLift P.isoModSerre.Q P M S T)) := by
  let := SubobjectIntervalLift.nonempty (L := P.isoModSerre.Q) (P := P) h
  exact classifyingSpace_contractible_of_semilatticeSup _

/-- The quotient structure arrow associated to an ambient Serre layer. -/
def layerStructureArrow {M : C} (A : Abelian.Devissage.Layer P M) :
    ((abelianExactStructure P.isoModSerre.Localization)).qZero ⟶
      (quotientMapQ P).obj (QConstruction.of (abelianExactStructure C).deflation
        (abelianExactStructure C).inflation M) :=
  (quotientInclusionZeroIso P).inv.app A.comma.left ≫ (quotientMapQ P).map A.comma.hom

/-- A layer's structure arrow is classified by the localized upper endpoint. -/
theorem layerStructureArrow_subobject {M : C} (A : Abelian.Devissage.Layer P M) :
    QConstruction.zeroArrowSubobject (layerStructureArrow P A) =
      subobjectMap P.isoModSerre.Q P M A.upper := by
  let e := ((quotient_isZero_obj_iff P A.quotient).2 A.property).iso
    (isZero_zero (P.isoModSerre.Localization))
  exact QConstruction.zeroArrowSubobject_comp_iso e.symm
    (((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P
      P.isoModSerre.Q)).toQCompatibleFunctor.mapSpan A.span)

/-- Lifts of a fixed quotient subobject by ambient Serre layers. This is the
concrete poset occurring in the structured zero-comma comparison. -/
abbrev ZeroLayerLift (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) :=
  {A : Abelian.Devissage.Layer P M //
    subobjectMap P.isoModSerre.Q P M A.lower = S ∧
    subobjectMap P.isoModSerre.Q P M A.upper = S}

/-- Intersection of lower endpoints and sum of upper endpoints give the
actual join of two lifts of the same quotient subobject. -/
def zeroLayerLiftSup {M : C} {S : Subobject (P.isoModSerre.Q.obj M)}
    (A B : ZeroLayerLift P M S) : ZeroLayerLift P M S := by
  let h : A.val.lower ⊓ B.val.lower ≤ A.val.upper ⊔ B.val.upper :=
    inf_le_left.trans (A.val.le.trans le_sup_left)
  refine ⟨{ lower := A.val.lower ⊓ B.val.lower
            upper := A.val.upper ⊔ B.val.upper
            le := h
            property := cokernel_ofLE_mem_of_subobjectMap_eq P.isoModSerre.Q P h ?_ }, ?_, ?_⟩
  · rw [subobjectMap_inf, subobjectMap_sup, A.property.1, B.property.1,
      A.property.2, B.property.2, inf_idem, sup_idem]
  · simp only [subobjectMap_inf, A.property.1, B.property.1, inf_idem]
  · simp only [subobjectMap_sup, A.property.2, B.property.2, sup_idem]

instance instSemilatticeSupZeroLayerLift (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) :
    SemilatticeSup (ZeroLayerLift P M S) where
  sup := zeroLayerLiftSup P
  le_sup_left _ _ := ⟨inf_le_left, le_sup_left⟩
  le_sup_right _ _ := ⟨inf_le_right, le_sup_right⟩
  sup_le _ _ _ h k := ⟨le_inf h.1 k.1, sup_le h.2 k.2⟩

/-- A single ambient subobject lift gives the diagonal Serre layer, so the
layer-lift poset is genuinely nonempty. -/
instance zeroLayerLift_nonempty (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) :
    Nonempty (ZeroLayerLift P M S) := by
  obtain ⟨A, hA⟩ := subobjectMap_surjective P.isoModSerre.Q P M S
  let T : Abelian.Devissage.Layer P M :=
    { lower := A
      upper := A
      le := le_rfl
      property := cokernel_ofLE_mem_of_subobjectMap_eq P.isoModSerre.Q P le_rfl rfl }
  exact ⟨⟨T, hA, hA⟩⟩

/-- The genuine realized layer-lift category is contractible by the explicit
join contraction; categorical connectedness is not used as a substitute. -/
theorem zeroLayerLift_contractible (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) :
    ContractibleSpace (ClassifyingSpace (ZeroLayerLift P M S)) :=
  classifyingSpace_contractible_of_semilatticeSup _

/-- The actual comma fiber of the inclusion into the source-zero comma category. -/
abbrev ZeroStructuredFiber (X : ZeroStructuredComma P) :=
  CostructuredArrow (serreToZeroStructuredComma P) X

instance zeroStructuredFiber_thin (X : ZeroStructuredComma P) :
    Quiver.IsThin (ZeroStructuredFiber P X) := by
  intro A B
  constructor
  intro f g
  apply CostructuredArrow.hom_ext
  apply (Abelian.Devissage.mapQ P).map_injective
  apply (cancel_mono B.hom.right).1
  exact (congrArg (fun k => k.right) (CostructuredArrow.w f)).trans
    (congrArg (fun k => k.right) (CostructuredArrow.w g)).symm

/-- A layer lifting the subobject classified by `X.hom` determines an object
of the actual comma fiber, using its quotient-to-ambient Q-span. -/
def zeroLayerToStructuredFiberObj (X : ZeroStructuredComma P)
    (A : ZeroLayerLift P X.right.obj.of (QConstruction.zeroArrowSubobject X.hom)) :
    ZeroStructuredFiber P X :=
  CostructuredArrow.mk (Y := A.val.comma.left)
    (StructuredArrow.homMk A.val.comma.hom (by
      change layerStructureArrow P A.val = X.hom
      apply QConstruction.zeroArrowSubobject_injective
      rw [layerStructureArrow_subobject]
      exact A.property.2))

/-- The actual layer comparison into the comma fiber. -/
def zeroLayerToStructuredFiber (X : ZeroStructuredComma P) :
    ZeroLayerLift P X.right.obj.of (QConstruction.zeroArrowSubobject X.hom) ⥤ ZeroStructuredFiber
      P X where
  obj := zeroLayerToStructuredFiberObj P X
  map f := CostructuredArrow.homMk (Abelian.Devissage.Layer.commaMap (leOfHom f)).left (by
    apply StructuredArrow.hom_ext
    exact CostructuredArrow.w (Abelian.Devissage.Layer.commaMap (leOfHom f)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

instance zeroLayerToStructuredFiber_faithful (X : ZeroStructuredComma P) :
    (zeroLayerToStructuredFiber P X).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance zeroLayerToStructuredFiber_full (X : ZeroStructuredComma P) :
    (zeroLayerToStructuredFiber P X).Full where
  map_surjective {A B} f := by
    let g : A.val.comma ⟶ B.val.comma := CostructuredArrow.homMk f.left (by
      exact congrArg (fun k => k.right) (CostructuredArrow.w f))
    exact ⟨homOfLE (Abelian.Devissage.Layer.le_of_comma_hom g), Subsingleton.elim _ _⟩

set_option backward.isDefEq.respectTransparency false in
instance zeroLayerToStructuredFiber_essSurj (X : ZeroStructuredComma P) :
    (zeroLayerToStructuredFiber P X).EssSurj where
  mem_essImage Y := by
    let M := X.right.obj.of
    let Z : Abelian.Devissage.QComma P M := CostructuredArrow.mk Y.hom.right
    let A := (Abelian.Devissage.layerToComma P M).objPreimage Z
    let e := (Abelian.Devissage.layerToComma P M).objObjPreimageIso Z
    have hw : layerStructureArrow P A = X.hom := by
      change (quotientInclusionZeroIso P).inv.app A.comma.left ≫
        (quotientMapQ P).map A.comma.hom = X.hom
      have he : (Abelian.Devissage.mapQ P).map e.hom.left ≫ Z.hom = A.comma.hom :=
        CostructuredArrow.w e.hom
      rw [← he, Functor.map_comp, ← Category.assoc]
      have hn : (quotientInclusionZeroIso P).inv.app A.comma.left ≫
          (quotientMapQ P).map ((Abelian.Devissage.mapQ P).map e.hom.left) =
          (quotientInclusionZeroIso P).inv.app Y.left := by
        have hn' := ((quotientInclusionZeroIso P).inv.naturality e.hom.left).symm
        change (quotientInclusionZeroIso P).inv.app A.comma.left ≫
          (quotientMapQ P).map ((Abelian.Devissage.mapQ P).map e.hom.left) =
          𝟙 _ ≫ (quotientInclusionZeroIso P).inv.app Y.left at hn'
        exact hn'.trans (Category.id_comp _)
      rw [hn]
      exact StructuredArrow.w Y.hom
    have hu : subobjectMap P.isoModSerre.Q P M A.upper = QConstruction.zeroArrowSubobject X.hom
      := by
      rw [← layerStructureArrow_subobject]
      exact congrArg QConstruction.zeroArrowSubobject hw
    have hl : subobjectMap P.isoModSerre.Q P M A.lower = QConstruction.zeroArrowSubobject X.hom :=
      (subobjectMap_eq_of_cokernel_ofLE_mem P.isoModSerre.Q P A.le A.property).trans hu
    refine ⟨⟨A, hl, hu⟩, ⟨CostructuredArrow.isoMk
      ((CostructuredArrow.proj (Abelian.Devissage.mapQ P) (QConstruction.of _ _ M)).mapIso e) ?_⟩⟩
    apply StructuredArrow.hom_ext
    exact CostructuredArrow.w e.hom

instance zeroLayerToStructuredFiber_isEquivalence (X : ZeroStructuredComma P) :
    (zeroLayerToStructuredFiber P X).IsEquivalence where

/-- The actual structured-comma fiber is equivalent to the explicitly
contractible layer-lift poset. -/
def zeroStructuredFiberEquivalence (X : ZeroStructuredComma P) :
    ZeroLayerLift P X.right.obj.of (QConstruction.zeroArrowSubobject X.hom) ≌ ZeroStructuredFiber
      P X :=
  (zeroLayerToStructuredFiber P X).asEquivalence

/-- Every actual comma fiber in the source-zero comparison is contractible. -/
theorem zeroStructuredFiber_contractible (X : ZeroStructuredComma P) :
    ContractibleSpace (ClassifyingSpace (ZeroStructuredFiber P X)) := by
  let := zeroLayerLift_contractible P X.right.obj.of (QConstruction.zeroArrowSubobject X.hom)
  exact (equivalenceClassifyingHomotopyEquiv (zeroStructuredFiberEquivalence P
    X)).symm.contractibleSpace

/-- Quillen's source-zero comma comparison is a genuine homotopy equivalence,
with the canonical inclusion lift as its forward map. -/
def zeroStructuredCommaClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (abelianExactStructure P.FullSubcategory).KSpace
      (ClassifyingSpace (ZeroStructuredComma P)) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (serreToZeroStructuredComma P)
    (zeroStructuredFiber_contractible P)

@[simp]
theorem zeroStructuredCommaClassifyingHomotopyEquiv_toFun :
    (zeroStructuredCommaClassifyingHomotopyEquiv P).toFun =
      (classifyingSpaceMap (serreToZeroStructuredComma P)).hom := rfl

/-- The isomorphism objects in a quotient structured comma category. -/
def isoStructureProperty (V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory) :
    ObjectProperty (StructuredArrow V (quotientMapQ P)) := fun X => IsIso X.hom

/-- The full subcategory of arrows from `V` to `quotientMapQ P` whose structure Q-arrow is an
isomorphism. -/
abbrev IsoStructuredComma (V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory) :=
  (isoStructureProperty P V).FullSubcategory

instance isoStructure_arrow_isIso {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    (A : IsoStructuredComma P V) : IsIso A.obj.hom := A.property

/-- Inclusion of the objects whose structure Q-arrow is invertible. -/
@[implicit_reducible]
def isoStructuredInclusion (V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory) :
    IsoStructuredComma P V ⥤ StructuredArrow V (quotientMapQ P) :=
  (isoStructureProperty P V).ι

/-- The costructured-arrow category of maps from isomorphism objects to a fixed quotient
structured-comma object `X`; this is the comma fiber of `isoStructuredInclusion P V` over
`X`. -/
abbrev IsoStructuredFiber {V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) := CostructuredArrow (isoStructuredInclusion P V) X

/-- The concrete interval-lift model for the comma fiber over `X`. -/
abbrev IsoFiberIntervals {V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) :=
  SubobjectIntervalLift P.isoModSerre.Q P X.right.obj.of
    (QConstruction.arrowLower X.hom) (QConstruction.arrowUpper X.hom)

/-- A lifted interval defines its ordinary quotient-to-ambient layer. -/
def isoFiberIntervalLayer {V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    Abelian.Devissage.Layer (⊤ : ObjectProperty C) X.right.obj.of where
  lower := A.lower
  upper := A.upper
  le := A.le
  property := trivial

/-- The actual ambient Q-arrow associated to a lifted interval. -/
def isoFiberIntervalArrow {V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      (isoFiberIntervalLayer P A).quotient ⟶ X.right :=
  QConstruction.mkHom _ _ (isoFiberIntervalLayer P A).span

@[simp]
theorem isoFiberIntervalArrow_lower {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    QConstruction.arrowLower (isoFiberIntervalArrow P A) = A.lower :=
      QConstruction.arrowLower_layerSpan _

@[simp]
theorem isoFiberIntervalArrow_upper {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    QConstruction.arrowUpper (isoFiberIntervalArrow P A) = A.upper :=
      QConstruction.arrowUpper_layerSpan _

/-- Completeness of the layer invariant identifies the localized source
with the required base object. This is an actual Q-isomorphism. -/
def isoFiberIntervalSourceIso {V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    (quotientMapQ P).obj (QConstruction.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation (isoFiberIntervalLayer P A).quotient) ≅ V :=
  (QConstruction.exists_qIso_of_endpoints_eq ((quotientMapQ P).map (isoFiberIntervalArrow P A))
    X.hom
    (by erw [arrowLower_quotientMapQ, isoFiberIntervalArrow_lower]; exact A.map_lower)
    (by erw [arrowUpper_quotientMapQ, isoFiberIntervalArrow_upper]; exact A.map_upper)).choose

/-- The chosen source identification commutes with the structure arrow. -/
lemma isoFiberIntervalSourceIso_hom_comp {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    (isoFiberIntervalSourceIso P A).hom ≫ X.hom =
      (quotientMapQ P).map (isoFiberIntervalArrow P A) :=
  (QConstruction.exists_qIso_of_endpoints_eq ((quotientMapQ P).map (isoFiberIntervalArrow P A))
    X.hom
    (by erw [arrowLower_quotientMapQ, isoFiberIntervalArrow_lower]; exact A.map_lower)
    (by erw [arrowUpper_quotientMapQ, isoFiberIntervalArrow_upper]; exact A.map_upper)).choose_spec

/-- An interval lift gives an object of the actual isomorphism-inclusion comma fiber. -/
def isoFiberIntervalObj {V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} (A : IsoFiberIntervals P X) :
    IsoStructuredFiber P X := by
  let Y : IsoStructuredComma P V :=
    ⟨StructuredArrow.mk (Y := QConstruction.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation (isoFiberIntervalLayer P A).quotient)
      (isoFiberIntervalSourceIso P A).inv, by dsimp [isoStructureProperty]; infer_instance⟩
  exact CostructuredArrow.mk (Y := Y)
    (StructuredArrow.homMk (isoFiberIntervalArrow P A) (by
      change (isoFiberIntervalSourceIso P A).inv ≫
        (quotientMapQ P).map (isoFiberIntervalArrow P A) = X.hom
      rw [← isoFiberIntervalSourceIso_hom_comp]
      simp))

/-- In the actual fiber, the Q-arrow into the fixed target determines every morphism. -/
instance isoStructuredFiber_thin {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : Quiver.IsThin (IsoStructuredFiber P X) := by
  intro A B
  constructor
  intro f g
  apply CostructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  apply (cancel_mono B.hom.right).1
  exact (congrArg (fun k => k.right) (CostructuredArrow.w f)).trans
    (congrArg (fun k => k.right) (CostructuredArrow.w g)).symm

set_option backward.isDefEq.respectTransparency false in
/-- An actual ambient Q-factorization uniquely lifts to a morphism of the
isomorphism-inclusion comma fibers. Its structure triangle follows by monicity. -/
def isoStructuredFiberHomMk {V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} {A B : IsoStructuredFiber P X}
    (k : A.left.obj.right ⟶ B.left.obj.right) (hk : k ≫ B.hom.right = A.hom.right) : A ⟶ B :=
  CostructuredArrow.homMk (ObjectProperty.homMk (StructuredArrow.homMk k (by
    have : Mono ((quotientMapQ P).map B.hom.right) :=
      QConstruction.abelianQ_mono (C := P.isoModSerre.Localization) _
    apply (cancel_mono ((quotientMapQ P).map B.hom.right)).1
    rw [Category.assoc, ← Functor.map_comp, hk]
    exact (StructuredArrow.w A.hom).trans (StructuredArrow.w B.hom).symm)))
    (by apply StructuredArrow.hom_ext; exact hk)

/-- A compatible source Q-isomorphism gives an actual isomorphism of comma fibers. -/
def isoStructuredFiberIsoMk {V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory}
    {X : StructuredArrow V (quotientMapQ P)} {A B : IsoStructuredFiber P X}
    (k : A.left.obj.right ≅ B.left.obj.right) (hk : k.hom ≫ B.hom.right = A.hom.right) : A ≅ B where
  hom := isoStructuredFiberHomMk P k.hom hk
  inv := isoStructuredFiberHomMk P k.inv (by rw [← hk]; simp)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The concrete interval comparison, using the actual Q-factorizations
classified by interval inequalities. -/
def intervalToIsoStructuredFiber {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : IsoFiberIntervals P X ⥤ IsoStructuredFiber P X where
  obj := isoFiberIntervalObj P
  map {A B} h := isoStructuredFiberHomMk P
    (QConstruction.exists_factor_of_endpoints_order (isoFiberIntervalArrow P A)
      (isoFiberIntervalArrow P B)
      (by simpa only [isoFiberIntervalArrow_lower] using (leOfHom h).1)
      (by simpa only [isoFiberIntervalArrow_upper] using (leOfHom h).2)).choose
    (QConstruction.exists_factor_of_endpoints_order (isoFiberIntervalArrow P A)
      (isoFiberIntervalArrow P B)
      (by simpa only [isoFiberIntervalArrow_lower] using (leOfHom h).1)
      (by simpa only [isoFiberIntervalArrow_upper] using (leOfHom h).2)).choose_spec
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

instance intervalToIsoStructuredFiber_faithful {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : (intervalToIsoStructuredFiber P X).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance intervalToIsoStructuredFiber_full {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : (intervalToIsoStructuredFiber P X).Full where
  map_surjective {A B} f := by
    have h := QConstruction.endpoints_order_of_fac (isoFiberIntervalArrow P A)
      (isoFiberIntervalArrow P B)
      f.left.hom.right (congrArg (fun k => k.right) (CostructuredArrow.w f))
    have hab : A ≤ B := by
      change B.lower ≤ A.lower ∧ A.upper ≤ B.upper
      simpa only [isoFiberIntervalArrow_lower, isoFiberIntervalArrow_upper] using h
    exact ⟨homOfLE hab, Subsingleton.elim _ _⟩

set_option backward.isDefEq.respectTransparency false in
instance intervalToIsoStructuredFiber_essSurj {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : (intervalToIsoStructuredFiber P X).EssSurj where
  mem_essImage Y := by
    let : IsIso Y.left.obj.hom := Y.left.property
    let g := Y.hom.right
    have hl : subobjectMap P.isoModSerre.Q P X.right.obj.of (QConstruction.arrowLower g) =
        QConstruction.arrowLower X.hom := by
      calc
        _ = QConstruction.arrowLower ((quotientMapQ P).map g) := (arrowLower_quotientMapQ P g).symm
        _ = QConstruction.arrowLower (Y.left.obj.hom ≫ (quotientMapQ P).map g) :=
          (QConstruction.arrowLower_comp_of_isIso Y.left.obj.hom _).symm
        _ = _ := congrArg QConstruction.arrowLower (StructuredArrow.w Y.hom)
    have hu : subobjectMap P.isoModSerre.Q P X.right.obj.of (QConstruction.arrowUpper g) =
        QConstruction.arrowUpper X.hom := by
      calc
        _ = QConstruction.arrowUpper ((quotientMapQ P).map g) := (arrowUpper_quotientMapQ P g).symm
        _ = QConstruction.arrowUpper (Y.left.obj.hom ≫ (quotientMapQ P).map g) :=
          (QConstruction.arrowUpper_comp_of_isIso Y.left.obj.hom _).symm
        _ = _ := congrArg QConstruction.arrowUpper (StructuredArrow.w Y.hom)
    let A : IsoFiberIntervals P X :=
      { lower := QConstruction.arrowLower g
        upper := QConstruction.arrowUpper g
        le := QConstruction.arrowLower_le_upper g
        map_lower := hl
        map_upper := hu }
    obtain ⟨e, he⟩ := QConstruction.exists_qIso_of_endpoints_eq (isoFiberIntervalArrow P A) g
      (isoFiberIntervalArrow_lower P A) (isoFiberIntervalArrow_upper P A)
    exact ⟨A, ⟨isoStructuredFiberIsoMk P e he⟩⟩

instance intervalToIsoStructuredFiber_isEquivalence {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) : (intervalToIsoStructuredFiber P X).IsEquivalence
      where

/-- The actual fiber of the inclusion of isomorphism objects is equivalent
to the concrete join-semilattice of ambient interval lifts. -/
def isoStructuredFiberEquivalence {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) :
    IsoFiberIntervals P X ≌ IsoStructuredFiber P X :=
  (intervalToIsoStructuredFiber P X).asEquivalence

/-- Every actual comma fiber of the isomorphism-object inclusion is
contractible by an explicit join contraction. -/
theorem isoStructuredFiber_contractible {V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory}
    (X : StructuredArrow V (quotientMapQ P)) :
    ContractibleSpace (ClassifyingSpace (IsoStructuredFiber P X)) := by
  let := subobjectIntervalLift_contractible P X.right.obj.of
    (QConstruction.arrowLower X.hom) (QConstruction.arrowUpper X.hom)
      (QConstruction.arrowLower_le_upper X.hom)
  exact (equivalenceClassifyingHomotopyEquiv (isoStructuredFiberEquivalence P
    X)).symm.contractibleSpace

/-- The inclusion of isomorphism objects into any quotient structured comma
category is a genuine homotopy equivalence. This is the first auxiliary lemma
of Quillen's localization proof, with its prescribed inclusion as forward map. -/
def isoStructuredInclusionClassifyingHomotopyEquiv (V : ((abelianExactStructure
  P.isoModSerre.Localization)).QCategory) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (IsoStructuredComma P V))
      (ClassifyingSpace (StructuredArrow V (quotientMapQ P))) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (isoStructuredInclusion P V)
    (isoStructuredFiber_contractible P)

@[simp]
theorem isoStructuredInclusionClassifyingHomotopyEquiv_toFun
    (V : ((abelianExactStructure P.isoModSerre.Localization)).QCategory) :
    (isoStructuredInclusionClassifyingHomotopyEquiv P V).toFun =
      (classifyingSpaceMap (isoStructuredInclusion P V)).hom := rfl

end CategoryTheory.ExactCategory.SerreLocalization
