/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.NestedWeakEquivalences
public import Colib.CategoryTheory.Waldhausen.Fibration.MixedChainReplacement
public import Colib.CategoryTheory.Waldhausen.Rows.JointFunctor
public import Colib.CategoryTheory.Waldhausen.Additivity.CoproductAlgebra

/-! # Genuine joint-cylinder factorizations on the original quotient rows

An exact base joint-arrow functor with its actual endpoint coproduct and
coarse-weak projection is lifted to the unchanged fine quotient rows.
The first endpoint is a genuine row cofibration by a displayed pointwise
coproduct pushout, and the joint arrow is a genuine Reedy row cofibration
by the accepted interchange theorem. No row factorization is assumed.


Implementation provenance:
`Quillen/Waldhausen/Fibration/Rows/JointFactorization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RowFactorization
variable {C : Type u} [Category.{v} C] {V : Structure C}

/-- Structural base-cylinder data, with actual endpoint coproduct maps and
an actual coarse-weak projection. Exactness refers only to the base category. -/
structure JointData (N : NestedWeakEquivalences V) where
  /-- The functor assigning a cofibration arrow to each original arrow, exact for the pointwise
  arrow and Reedy extension Waldhausen structures. -/
  joint : Arrow C ⥤ ExtensionCategory.Obj V
  exact : IsExact (ArrowCategory.waldhausenStructure V).cof
    (ArrowCategory.waldhausenStructure V).weq
    (ExtensionCategory.waldhausenStructure V).cof
    (ExtensionCategory.waldhausenStructure V).weq joint
  /-- The natural map from the original arrow source into the source of its joint cofibration
  arrow. -/
  inl : Arrow.leftFunc ⟶ joint ⋙ ExtensionCategory.source V
  /-- The natural map from the original arrow target into the source of its joint cofibration
  arrow. -/
  inr : Arrow.rightFunc ⟶ joint ⋙ ExtensionCategory.source V
  /-- The colimit witness identifying each joint source as the coproduct of the original source
  and target with the specified endpoint maps. -/
  coproduct (f : Arrow C) : IsColimit (BinaryCofan.mk (inl.app f) (inr.app f))
  /-- The natural map from the joint middle object to the original arrow target, required to be
  a coarse weak equivalence. -/
  projection : joint ⋙ ExtensionCategory.middle V ⟶ Arrow.rightFunc
  factorization (f : Arrow C) :
    inl.app f ≫ (joint.obj f).obj.hom ≫ projection.app f = f.hom
  weak (f : Arrow C) : N.coarse.weq (projection.app f)

variable (N : NestedWeakEquivalences V) (D : JointData N)

/-- The original joint functor on actual quotient rows. -/
abbrev jointOnRows (n : SimplexCategory) := QuotientRows.jointOnRows V V D.exact n

/-- Its original source row, the actual endpoint sum. -/
def source (n : SimplexCategory) : Arrow (QuotientRows.Obj V n) ⥤ QuotientRows.Obj V n :=
  jointOnRows N D n ⋙ ExtensionCategory.source (QuotientRows.waldhausenStructure V n)

/-- Its original middle row. -/
def middle (n : SimplexCategory) : Arrow (QuotientRows.Obj V n) ⥤ QuotientRows.Obj V n :=
  jointOnRows N D n ⋙ ExtensionCategory.middle (QuotientRows.waldhausenStructure V n)

/-- The actual first endpoint injection, with unchanged component maps. -/
def first (n : SimplexCategory) : Arrow.leftFunc ⟶ source N D n where
  app f := (QuotientRows.objects V n).homMk
    (Functor.whiskerLeft ((QuotientRows.arrowDiagram V n).obj f) D.inl)
  naturality f g α := by
    apply ObjectProperty.hom_ext
    ext p
    exact D.inl.naturality (((QuotientRows.arrowDiagram V n).map α).app p)

/-- The actual second endpoint injection, with unchanged component maps. -/
def second (n : SimplexCategory) : Arrow.rightFunc ⟶ source N D n where
  app f := (QuotientRows.objects V n).homMk
    (Functor.whiskerLeft ((QuotientRows.arrowDiagram V n).obj f) D.inr)
  naturality f g α := by
    apply ObjectProperty.hom_ext
    ext p
    exact D.inr.naturality (((QuotientRows.arrowDiagram V n).map α).app p)

/-- The actual endpoint-sum square is a pushout in the original full row category. -/
theorem endpoint_isPushout {n : SimplexCategory} (f : Arrow (QuotientRows.Obj V n)) :
    IsPushout ((QuotientRows.isZero V n).to_ f.left)
      ((QuotientRows.isZero V n).to_ f.right) ((first N D n).app f) ((second N D n).app f) := by
  apply QuotientRows.isPushout_of_pointwise V
  intro p
  convert! IsPushout.of_is_coproduct (D.coproduct (Arrow.mk (f.hom.hom.app p)))
    V.isZero.isInitial using 1 <;>
    exact V.isZero.eq_of_src _ _

/-- The actual joint-source row is canonically the endpoint coproduct. -/
def sourceCoproductIso {n : SimplexCategory} [HasBinaryCoproducts (QuotientRows.Obj V n)]
    (f : Arrow (QuotientRows.Obj V n)) : f.left ⨿ f.right ≅ (source N D n).obj f :=
  (Additivity.coprod_isPushout (QuotientRows.waldhausenStructure V n) f.left f.right).isoIsPushout
    _ _ (endpoint_isPushout N D f)

@[reassoc (attr := simp)] theorem sourceCoproductIso_inl {n : SimplexCategory}
    [HasBinaryCoproducts (QuotientRows.Obj V n)] (f : Arrow (QuotientRows.Obj V n)) :
    coprod.inl ≫ (sourceCoproductIso N D f).hom = (first N D n).app f :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

@[reassoc (attr := simp)] theorem sourceCoproductIso_inr {n : SimplexCategory}
    [HasBinaryCoproducts (QuotientRows.Obj V n)] (f : Arrow (QuotientRows.Obj V n)) :
    coprod.inr ≫ (sourceCoproductIso N D f).hom = (second N D n).app f :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

/-- The first endpoint inclusion satisfies the genuine all-triples Reedy condition. -/
theorem first_cof {n : SimplexCategory} (f : Arrow (QuotientRows.Obj V n)) :
    QuotientRows.cof V n ((first N D n).app f) :=
  (QuotientRows.waldhausenStructure V n).cof_pushout
    (QuotientRows.cof_zero V n f.right) (endpoint_isPushout N D f).flip

/-- The actual first cylinder factor on quotient rows. -/
def inclusion (n : SimplexCategory) : Arrow.leftFunc ⟶ middle N D n :=
  first N D n ≫ Functor.whiskerLeft (jointOnRows N D n)
    (ExtensionCategory.inclusion (QuotientRows.waldhausenStructure V n))

/-- The original projection, applied at each unchanged quotient component. -/
def projection (n : SimplexCategory) : middle N D n ⟶ Arrow.rightFunc where
  app f := (QuotientRows.objects V n).homMk
    (Functor.whiskerLeft ((QuotientRows.arrowDiagram V n).obj f) D.projection)
  naturality f g α := by
    apply ObjectProperty.hom_ext
    ext p
    exact D.projection.naturality (((QuotientRows.arrowDiagram V n).map α).app p)

/-- The original middle functor is genuinely exact for the fine row structures. -/
theorem middle_exact (n : SimplexCategory) :
    IsExact (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure V n)).cof
      (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure V n)).weq
      (QuotientRows.waldhausenStructure V n).cof (QuotientRows.waldhausenStructure V n).weq
      (middle N D n) :=
  (QuotientRows.jointOnRows_exact V V D.exact n).comp
    (ExtensionCategory.middle_exact (QuotientRows.waldhausenStructure V n))

/-- The actual original row factorization, with the unchanged Reedy cofibration class. -/
def factorization (n : SimplexCategory) : FunctorialFactorization
    (RowWeakEquivalences.coarseStructure N n) where
  middle := middle N D n
  inclusion := inclusion N D n
  projection := projection N D n
  factorization f := by
    apply ObjectProperty.hom_ext
    ext p
    change (D.inl.app (Arrow.mk (f.hom.hom.app p)) ≫
      (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.hom) ≫
        D.projection.app (Arrow.mk (f.hom.hom.app p)) = _
    simpa only [Category.assoc] using! D.factorization (Arrow.mk (f.hom.hom.app p))
  cofibration f :=
    (QuotientRows.waldhausenStructure V n).cof.comp_mem _ _ (first_cof N D f)
      ((jointOnRows N D n).obj f).property
  weak f p := D.weak (Arrow.mk (f.hom.hom.app p))

/-- Coarse exactness of the original middle functor, derived from its actual weak projection. -/
theorem middle_coarse_exact (n : SimplexCategory) [N.coarse.weq.HasTwoOutOfThreeProperty] :
    IsExact (ArrowCategory.waldhausenStructure (RowWeakEquivalences.coarseStructure N n)).cof
      (ArrowCategory.waldhausenStructure (RowWeakEquivalences.coarseStructure N n)).weq
      (RowWeakEquivalences.coarseStructure N n).cof (RowWeakEquivalences.coarseStructure N n).weq
      (middle N D n) where
  zero := (middle_exact N D n).zero
  cofibration := (middle_exact N D n).cofibration
  weak α hα := by
    apply (RowWeakEquivalences.coarseStructure N n).weq.of_postcomp _
      ((projection N D n).app _) ((factorization N D n).weak _)
    rw [(projection N D n).naturality]
    exact (RowWeakEquivalences.coarseStructure N n).weq.comp_mem _ _
      ((factorization N D n).weak _) hα.2
  pushout := (middle_exact N D n).pushout

/-- Fine-square preservation follows from genuine middle exactness, without fine saturation. -/
theorem factorization_fineSquares (n : SimplexCategory) :
    MixedChainReplacement.PreservesFineSquares (RowWeakEquivalences.nested N n) (factorization N
      D n) := by
  intro f g α hl hr
  exact (middle_exact N D n).weak α ⟨hl, hr⟩

@[simp] theorem factorization_middle_obj_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((factorization N D n).middle.obj f).obj.obj p) =
      (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.right := rfl

@[simp] theorem factorization_middle_map_component {n : SimplexCategory}
    {f g : Arrow (QuotientRows.Obj V n)} (α : f ⟶ g) (p : Interval n) :
    (((factorization N D n).middle.map α).hom.app p) =
      (D.joint.map (((QuotientRows.arrowDiagram V n).map α).app p)).hom.right := rfl

@[simp] theorem factorization_inclusion_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((factorization N D n).inclusion.app f).hom.app p) =
      D.inl.app (Arrow.mk (f.hom.hom.app p)) ≫
        (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.hom := rfl

@[simp] theorem factorization_projection_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((factorization N D n).projection.app f).hom.app p) =
      D.projection.app (Arrow.mk (f.hom.hom.app p)) := rfl

/-- Every ordinal restriction commutes strictly with the original middle functor. -/
@[simp] theorem middle_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    (QuotientRows.reindex V α).mapArrow ⋙ middle N D m =
      middle N D n ⋙ QuotientRows.reindex V α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem inclusion_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (f : Arrow (QuotientRows.Obj V n)) :
    (QuotientRows.reindex V α).map ((factorization N D n).inclusion.app f) =
      (factorization N D m).inclusion.app ((QuotientRows.reindex V α).mapArrow.obj f) := rfl

@[simp] theorem projection_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (f : Arrow (QuotientRows.Obj V n)) :
    (QuotientRows.reindex V α).map ((factorization N D n).projection.app f) =
      (factorization N D m).projection.app ((QuotientRows.reindex V α).mapArrow.obj f) := rfl

end CategoryTheory.Waldhausen.Fibration.RowFactorization
