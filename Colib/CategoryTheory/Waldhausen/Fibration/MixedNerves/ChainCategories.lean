/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.FineChains
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.FiltrationWeakEquivalence
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.ChainReplacement

/-! # Both original directions of the mixed chain nerves

The coarse-chain objects and their cofibration subcategory are the previously
constructed original categories. The transposed direction uses actual
fine-weak chains and pointwise coarse (or coarse-cofibration) maps.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/ChainCategories.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration.RelativeRows


noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
open RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Original fine morphisms between the existing coarse-weak chains. -/
def coarseChainFineWeak (n : SimplexCategory) : MorphismProperty (CoarseWeakChain N n) :=
  pointwise V.weq (coarseWeakChains N n)
instance coarseChainFineWeak_multiplicative (n : SimplexCategory) :
    (coarseChainFineWeak N n).IsMultiplicative := pointwise_multiplicative _ _
/-- The category of coarse-weak chains in simplicial degree `n`, retaining only natural
transformations that are pointwise fine weak equivalences. -/
abbrev FineWeakCoarseChains (n : SimplexCategory) := WideSubcategory (coarseChainFineWeak N n)

/-- Original coarse-weak transformations between actual fine-weak chains. -/
abbrev HorizontalChains (k : SimplexCategory) := WideSubcategory (pointwiseCoarse N k)
/-- The same objects with genuine pointwise weak cofibrations. -/
abbrev HorizontalCofChains (k : SimplexCategory) :=
  WideSubcategory (pointwiseCof V k ⊓ pointwiseCoarse N k)

/-- Forget only the original coarse-chain cofibration predicate. -/
def forgetCofChain (n : SimplexCategory) : CofibrationWeakChain N n ⥤ CoarseWeakChain N n where
  obj F := ⟨F.obj, F.property.2⟩
  map f := (coarseWeakChains N n).homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl
/-- The actual inclusion in the original fine-weak nerve direction. -/
def weakForgetCofChain (n : SimplexCategory) : FineWeakChains N n ⥤ FineWeakCoarseChains N n where
  obj F := ⟨(forgetCofChain N n).obj F.obj⟩
  map f := ⟨(forgetCofChain N n).map f.hom, f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl
/-- The actual inclusion in the transposed coarse-arrow direction. -/
def horizontalInclusion (k : SimplexCategory) : HorizontalCofChains N k ⥤ HorizontalChains N k where
  obj F := ⟨F.obj⟩
  map f := ⟨f.hom, f.property.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Literal ordinal restriction of the existing coarse-weak chains. -/
def coarseChainReindex {m n : SimplexCategory} (α : m ⟶ n) : CoarseWeakChain N n ⥤
    CoarseWeakChain N m where
  obj F := ⟨(SimplexCategory.toCat.map α).toFunctor ⋙ F.obj,
    fun f ↦ F.property ((SimplexCategory.toCat.map α).toFunctor.map f)⟩
  map f := (coarseWeakChains N m).homMk
    (Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl
/-- Literal ordinal restriction retains both original coarse-chain predicates. -/
def cofChainReindex {m n : SimplexCategory} (α : m ⟶ n) : CofibrationWeakChain N n ⥤
    CofibrationWeakChain N m where
  obj F := ⟨(SimplexCategory.toCat.map α).toFunctor ⋙ F.obj,
    ⟨fun f ↦ F.property.1 ((SimplexCategory.toCat.map α).toFunctor.map f),
      fun f ↦ F.property.2 ((SimplexCategory.toCat.map α).toFunctor.map f)⟩⟩
  map f := (cofibrationWeakChains N m).homMk
    (Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original pointwise fine-weak maps remain unchanged under restriction. -/
def fineWeakCoarseReindex {m n : SimplexCategory} (α : m ⟶ n) :
    FineWeakCoarseChains N n ⥤ FineWeakCoarseChains N m where
  obj F := ⟨(coarseChainReindex N α).obj F.obj⟩
  map f := ⟨(coarseChainReindex N α).map f.hom, fun i ↦ f.property (α.toOrderHom i)⟩
  map_id _ := rfl
  map_comp _ _ := rfl
/-- The accepted fine-weak cofibration-chain category restricts by original components. -/
def fineWeakCofReindex {m n : SimplexCategory} (α : m ⟶ n) : FineWeakChains N n ⥤ FineWeakChains
    N m where
  obj F := ⟨(cofChainReindex N α).obj F.obj⟩
  map f := ⟨(cofChainReindex N α).map f.hom, fun i ↦ f.property (α.toOrderHom i)⟩
  map_id _ := rfl
  map_comp _ _ := rfl
/-- Fine-index restriction of the transposed coarse-arrow category. -/
def horizontalReindex {k l : SimplexCategory} (α : k ⟶ l) : HorizontalChains N l ⥤
    HorizontalChains N k where
  obj F := ⟨(fineReindex V α).obj F.obj⟩
  map f := ⟨(fineReindex V α).map f.hom,
    fineReindex_coarse (N := N) (V := V) α f.hom f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl
/-- Fine-index restriction of the transposed weak-cofibration category. -/
def horizontalCofReindex {k l : SimplexCategory} (α : k ⟶ l) :
    HorizontalCofChains N l ⥤ HorizontalCofChains N k where
  obj F := ⟨(fineReindex V α).obj F.obj⟩
  map f := ⟨(fineReindex V α).map f.hom,
    ⟨fineReindex_cof V α f.hom f.property.1,
      fineReindex_coarse (N := N) (V := V) α f.hom f.property.2⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Original fine-weak categories indexed by coarse-chain degree. -/
def coarseChainCategories : SimplexCategoryᵒᵖ ⥤ Cat.{v, max u v} where
  obj n := Cat.of (FineWeakCoarseChains N n.unop)
  map α := Cat.Hom.ofFunctor (fineWeakCoarseReindex N α.unop)
  map_id _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- Original fine-weak cofibration-chain categories indexed by coarse-chain degree. -/
def cofChainCategories : SimplexCategoryᵒᵖ ⥤ Cat.{v, max u v} where
  obj n := Cat.of (FineWeakChains N n.unop)
  map α := Cat.Hom.ofFunctor (fineWeakCofReindex N α.unop)
  map_id _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- Actual coarse-arrow categories indexed by fine-chain degree. -/
def horizontalCategories : SimplexCategoryᵒᵖ ⥤ Cat.{v, max u v} where
  obj k := Cat.of (HorizontalChains N k.unop)
  map α := Cat.Hom.ofFunctor (horizontalReindex N α.unop)
  map_id _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- Actual weak-cofibration categories indexed by fine-chain degree. -/
def horizontalCofCategories : SimplexCategoryᵒᵖ ⥤ Cat.{v, max u v} where
  obj k := Cat.of (HorizontalCofChains N k.unop)
  map α := Cat.Hom.ofFunctor (horizontalCofReindex N α.unop)
  map_id _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The simplicial family of nerves of coarse-weak chain categories with pointwise fine-weak
morphisms; the outer index records coarse-chain degree. -/
def coarseChainNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := coarseChainCategories N ⋙ nerveFunctor
/-- The simplicial family of nerves of coarse-weak cofibration-chain categories with pointwise
fine-weak morphisms. -/
def cofChainNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := cofChainCategories N ⋙ nerveFunctor
/-- The simplicial family of nerves of fine-weak chain categories with pointwise coarse-weak
morphisms; the outer index records fine-chain degree. -/
def horizontalNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := horizontalCategories N ⋙ nerveFunctor
/-- The simplicial family of nerves of fine-weak chain categories with pointwise morphisms that
are both cofibrations and coarse weak equivalences. -/
def horizontalCofNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := horizontalCofCategories N ⋙
    nerveFunctor

/-- The original inclusion is natural in both original indices. -/
def chainInclusion : cofChainNerve N ⟶ coarseChainNerve N where
  app n := nerveMap (weakForgetCofChain N n.unop)
  naturality _ _ _ := by ext k F; rfl
/-- The same literal inclusion in the transposed presentation. -/
def horizontalNerveInclusion : horizontalCofNerve N ⟶ horizontalNerve N where
  app k := nerveMap (horizontalInclusion N k.unop)
  naturality _ _ _ := by ext n F; rfl

end CategoryTheory.Waldhausen.Fibration.MixedNerves
