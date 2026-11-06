/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryImages
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryBaseChange
public import Colib.Topology.ClassifyingSpace.FactorContraction
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-! # Contraction of the image-index structured kernel commas -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.SerreLocalization

open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Abelian
attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{u} C] [Abelian C]
variable (P : ObjectProperty C) [P.IsSerreClass]
variable (N : C) (T : (abelianExactStructure P.FullSubcategory).QCategory)
  (I : SerreImagePoset P N)

/-- The image-index comma in which all images contain the specified subobject. -/
abbrev ImageKernelComma := StructuredArrow I (auxiliaryKernelCommaImageFunctor P N T)

/-- Pullback to the prescribed image subobject is epimorphic, on all
objects and on the actual Q-span morphisms. -/
@[implicit_reducible]
def imageKernelPullback : ImageKernelComma P N T I ⥤ EpiAuxiliaryKernel P (I.val : C) where
  obj X := ⟨(overBaseChangeQ I.val.arrow).obj X.right.left.obj,
    overBaseChange_isoModSerre P I.val.arrow X.right.left.obj.obj.of X.right.left.property,
    pullback_to_image_epi X.right.left.obj.obj.of I.val (leOfHom X.hom)⟩
  map f := ObjectProperty.homMk ((overBaseChangeQ I.val.arrow).map f.right.left.hom)
  map_id X := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ I.val.arrow).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ I.val.arrow).map_comp _ _

/-- The underlying full auxiliary object of the structured image comma. -/
@[implicit_reducible]
def imageKernelProjection : ImageKernelComma P N T I ⥤ AuxiliaryKernel P N :=
  StructuredArrow.proj _ _ ⋙ CostructuredArrow.proj _ _

/-- Pullback preserves the actual kernel functor naturally on Q-arrows. -/
def imageKernelPullbackIso :
    imageKernelPullback P N T I ⋙ epiAuxiliaryKernelFunctor P (I.val : C) ≅
      imageKernelProjection P N T I ⋙ auxiliaryKernelFunctor P N :=
  NatIso.ofComponents
    (fun X => (auxiliaryBaseChangeKernelIso P I.val.arrow).app X.right.left) (by
    intro X Y f
    exact (auxiliaryBaseChangeKernelIso P I.val.arrow).hom.naturality f.right.left)


/-- The actual kernel-comma pullback functor, using the proved kernel comparison. -/
@[implicit_reducible]
def imageKernelCommaRetraction : ImageKernelComma P N T I ⥤ EpiKernelComma P (I.val : C) T where
  obj X := CostructuredArrow.mk ((imageKernelPullbackIso P N T I).hom.app X ≫ X.right.hom)
  map {X Y} f := CostructuredArrow.homMk ((imageKernelPullback P N T I).map f) (by
    change (epiAuxiliaryKernelFunctor P (I.val : C)).map ((imageKernelPullback P N T I).map f) ≫
        ((imageKernelPullbackIso P N T I).hom.app Y ≫ Y.right.hom) = _
    calc
      _ = ((imageKernelPullbackIso P N T I).hom.app X ≫
          (auxiliaryKernelFunctor P N).map f.right.left) ≫ Y.right.hom := by
        rw [← Category.assoc]
        exact congrArg (· ≫ Y.right.hom) ((imageKernelPullbackIso P N T I).hom.naturality f)
      _ = _ := by
        rw [Category.assoc]
        exact congrArg ((imageKernelPullbackIso P N T I).hom.app X ≫ ·) (CostructuredArrow.w
          f.right))
  map_id X := by apply CostructuredArrow.hom_ext; exact (imageKernelPullback P N T I).map_id _
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact (imageKernelPullback P N T I).map_comp f g


/-- Postcomposing an epimorphism onto the selected subobject gives exactly
that image in the fixed ambient base. -/
lemma epiAuxiliary_postcompose_image (X : EpiAuxiliaryKernel P (I.val : C)) :
    I.val ≤ imageSubobject (X.obj.obj.of.hom ≫ I.val.arrow) := by
  rw [imageSubobject_epi_comp, imageSubobject_mono, Subobject.mk_arrow]

/-- Postcomposition of epimorphic auxiliary extensions to the full base. -/
@[implicit_reducible]
def imageKernelPostcompose : EpiAuxiliaryKernel P (I.val : C) ⥤ AuxiliaryKernel P N :=
  epiAuxiliaryInclusion P (I.val : C) ⋙ auxiliaryPostcompose P I.val.arrow I.property

/-- The kernel comparison of the section functor. -/
def imageKernelPostcomposeIso :
    imageKernelPostcompose P N I ⋙ auxiliaryKernelFunctor P N ≅
      epiAuxiliaryKernelFunctor P (I.val : C) :=
  NatIso.ofComponents
    (fun X => (auxiliaryPostcomposeKernelIso P I.val.arrow I.property).app
      ((epiAuxiliaryInclusion P (I.val : C)).obj X))
    (fun f => (auxiliaryPostcomposeKernelIso P I.val.arrow I.property).hom.naturality
      ((epiAuxiliaryInclusion P (I.val : C)).map f))

/-- Postcomposition on the actual kernel commas. -/
@[implicit_reducible]
def imageKernelCommaPostcompose : EpiKernelComma P (I.val : C) T ⥤ AuxiliaryKernelComma P N T where
  obj X := CostructuredArrow.mk (Y := (imageKernelPostcompose P N I).obj X.left)
    ((imageKernelPostcomposeIso P N I).hom.app X.left ≫ X.hom)
  map {X Y} f := CostructuredArrow.homMk ((imageKernelPostcompose P N I).map f.left) (by
    change (auxiliaryKernelFunctor P N).map ((imageKernelPostcompose P N I).map f.left) ≫
      ((imageKernelPostcomposeIso P N I).hom.app Y.left ≫ Y.hom) =
      (imageKernelPostcomposeIso P N I).hom.app X.left ≫ X.hom
    calc
      _ = ((imageKernelPostcomposeIso P N I).hom.app X.left ≫
          (epiAuxiliaryKernelFunctor P (I.val : C)).map f.left) ≫ Y.hom := by
        rw [← Category.assoc]
        exact congrArg (· ≫ Y.hom) ((imageKernelPostcomposeIso P N I).hom.naturality f.left)
      _ = _ := by rw [Category.assoc, CostructuredArrow.w f])
  map_id X := by apply CostructuredArrow.hom_ext; exact (imageKernelPostcompose P N I).map_id _
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact (imageKernelPostcompose P N I).map_comp f.left g.left

/-- The section retains the image-index arrow as well as the kernel Q-arrow. -/
@[implicit_reducible]
def imageKernelCommaSection : EpiKernelComma P (I.val : C) T ⥤ ImageKernelComma P N T I where
  obj X := StructuredArrow.mk (Y := (imageKernelCommaPostcompose P N T I).obj X)
    (homOfLE (epiAuxiliary_postcompose_image P N I X.left))
  map f := StructuredArrow.homMk ((imageKernelCommaPostcompose P N T I).map f) (Subsingleton.elim _
    _)
  map_id X := by apply StructuredArrow.hom_ext; exact (imageKernelCommaPostcompose P N T I).map_id _
  map_comp f g := by
    apply StructuredArrow.hom_ext
    exact (imageKernelCommaPostcompose P N T I).map_comp f g

/-- The canonical pullback inclusion supplies a natural transformation from
the section of the retraction to the identity on the full structured image comma. -/
def imageKernelCommaCounit :
    imageKernelCommaRetraction P N T I ⋙ imageKernelCommaSection P N T I ⟶
      𝟭 (ImageKernelComma P N T I) where
  app X := StructuredArrow.homMk
    (CostructuredArrow.homMk
      ((auxiliaryBaseChangeCounit P I.val.arrow I.property).app X.right.left) (by
      change (auxiliaryKernelFunctor P N).map
          ((auxiliaryBaseChangeCounit P I.val.arrow I.property).app X.right.left) ≫ X.right.hom =
        (auxiliaryPostcomposeKernelIso P I.val.arrow I.property).hom.app
          ((auxiliaryBaseChange P I.val.arrow).obj X.right.left) ≫
          ((auxiliaryBaseChangeKernelIso P I.val.arrow).hom.app X.right.left ≫ X.right.hom)
      rw [auxiliaryBaseChangeCounit_kernel, Category.assoc])) (Subsingleton.elim _ _)
  naturality X Y f := by
    apply StructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    exact (auxiliaryBaseChangeCounit P I.val.arrow I.property).naturality f.right.left

/-- Every structured comma of the image projection contracts through the
actual epimorphic kernel comma over its indexing subobject. -/
theorem imageKernelComma_contractible :
    ContractibleSpace (ClassifyingSpace (ImageKernelComma P N T I)) := by
  let := epiKernelComma_contractible P (I.val : C) T
  exact classifyingSpace_contractible_of_factor_natTrans
    (imageKernelCommaRetraction P N T I) (imageKernelCommaSection P N T I)
    (imageKernelCommaCounit P N T I)

/-- The full auxiliary kernel comma is contractible. Its image projection
has contractible structured commas and a terminal indexing subobject. -/
theorem auxiliaryKernelComma_contractible :
    ContractibleSpace (ClassifyingSpace (AuxiliaryKernelComma P N T)) := by
  let := auxiliaryImagePoset_contractible P N
  exact TheoremA.contractibleSpace_of_structured_comma (auxiliaryKernelCommaImageFunctor P N T)
    (imageKernelComma_contractible P N T)

/-- The actual kernel functor on all Serre-isomorphisms into the fixed base
is a classifying-space homotopy equivalence. -/
def auxiliaryKernelClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
      (ClassifyingSpace (abelianExactStructure P.FullSubcategory).QCategory) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (auxiliaryKernelFunctor P N)
    (auxiliaryKernelComma_contractible P N)

@[simp]
theorem auxiliaryKernelClassifyingHomotopyEquiv_toFun :
    (auxiliaryKernelClassifyingHomotopyEquiv P N).toFun =
      (classifyingSpaceMap (auxiliaryKernelFunctor P N)).hom := rfl

end CategoryTheory.ExactCategory.SerreLocalization
