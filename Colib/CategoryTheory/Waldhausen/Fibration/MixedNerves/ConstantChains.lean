/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.ChainCategories
public import Colib.CategoryTheory.Waldhausen.Fibration.TrivialCofibrations.Category
public import Colib.Topology.ClassifyingSpace.Contraction

/-! # The original constant fine-chain inclusion

At every fixed fine degree, evaluation at zero retracts the original constant
chain inclusion. The original fine arrows from zero to each vertex give an
actual coarse natural transformation from the other composite to identity.
Only the forward constant inclusion is asserted to be ordinal-natural.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/ConstantChains.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
section Categorical
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- The actual constant diagram satisfies the fine object condition by identities. -/
def constantFineChain (k : SimplexCategory) : C ⥤ FineChain V k :=
  (fineChains V k).lift (Functor.const (Fin (k.len+1))) (fun X {_ _} _ ↦ V.weq.id_mem X)

variable {V} (N : NestedWeakEquivalences V)

/-- Original coarse weak arrows are retained as constant transformations of fine chains. -/
def constantHorizontal (k : SimplexCategory) : TrivialCofibrations.WeakCategory N.coarse.weq ⥤
    HorizontalChains N k where
  obj X := ⟨(constantFineChain V k).obj X.obj⟩
  map f := ⟨(constantFineChain V k).map f.hom, fun _ ↦ f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Original evaluation at the first vertex, retaining its actual coarse weak map. -/
def evaluateHorizontalZero (k : SimplexCategory) : HorizontalChains N k ⥤
    TrivialCofibrations.WeakCategory N.coarse.weq where
  obj F := ⟨F.obj.obj.obj 0⟩
  map f := ⟨f.hom.hom.app 0, f.property 0⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation of an original constant diagram is strictly the original object and arrow. -/
@[simp] theorem constantHorizontal_evaluateZero (k : SimplexCategory) :
    constantHorizontal N k ⋙ evaluateHorizontalZero N k = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The original chain arrows from the first vertex give an actual natural transformation. -/
def constantInitial (k : SimplexCategory) :
    evaluateHorizontalZero N k ⋙ constantHorizontal N k ⟶ 𝟭 (HorizontalChains N k) where
  app F := ⟨(fineChains V k).homMk {
    app i := F.obj.obj.map (homOfLE (Fin.zero_le i))
    naturality i j f := by
      change 𝟙 _ ≫ F.obj.obj.map _ = F.obj.obj.map _ ≫ F.obj.obj.map f
      rw [Category.id_comp, ← F.obj.obj.map_comp]
      rfl }, fun i ↦ N.le_weq _ (F.obj.property (homOfLE (Fin.zero_le i)))⟩
  naturality F G f := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext i
    exact (f.hom.hom.naturality (homOfLE (Fin.zero_le i))).symm

/-- Its components are exactly the original fine chain arrows, viewed in the coarse class. -/
@[simp] theorem constantInitial_app (k : SimplexCategory) (F : HorizontalChains N k) (i : Fin
    (k.len + 1)) :
    ((constantInitial N k).app F).hom.hom.app i = F.obj.obj.map (homOfLE (Fin.zero_le i)) := rfl

/-- Constant chains, unlike the chosen first-vertex inverse, commute strictly with every ordinal
restriction. -/
@[simp] theorem constantHorizontal_reindex {k l : SimplexCategory} (α : k ⟶ l) :
    constantHorizontal N l ⋙ horizontalReindex N α = constantHorizontal N k := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end Categorical

section Realization
-- This bound makes the original object and finite-chain categories share the
-- realization API's object universe while leaving hom universes independent.
variable {C : Type (max u v)} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (k : SimplexCategory)

/-- The original constant-chain nerve map is natural in the fine index. -/
def constantHorizontalNerve :
    (Functor.const SimplexCategoryᵒᵖ).obj (nerve (TrivialCofibrations.WeakCategory N.coarse.weq)) ⟶
      horizontalNerve N where
  app k := nerveMap (constantHorizontal N k.unop)
  naturality _ _ _ := by ext n F; rfl

/-- The actual constant-chain map is a genuine rowwise classifying-space homotopy equivalence. -/
def constantHorizontalClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (TrivialCofibrations.WeakCategory N.coarse.weq))
      (ClassifyingSpace (HorizontalChains N k)) where
  toFun := (classifyingSpaceMap (constantHorizontal N k)).hom
  invFun := (classifyingSpaceMap (evaluateHorizontalZero N k)).hom
  left_inv := by
    have h := congrArg (fun F ↦ (classifyingSpaceMap F).hom) (constantHorizontal_evaluateZero N k)
    rw [classifyingSpaceMap_comp, TopCat.hom_comp, classifyingSpaceMap_id, TopCat.hom_id] at h
    rw [h]
  right_inv := ⟨by
    simpa only [classifyingSpaceMap_comp, TopCat.hom_comp, classifyingSpaceMap_id,
      TopCat.hom_id] using
      classifyingSpaceNaturalTransformationHomotopy (constantInitial N k)⟩

@[simp] theorem constantHorizontalClassifyingHomotopyEquiv_toFun :
    (constantHorizontalClassifyingHomotopyEquiv N k).toFun =
      (classifyingSpaceMap (constantHorizontal N k)).hom := rfl

@[simp] theorem constantHorizontalClassifyingHomotopyEquiv_invFun :
    (constantHorizontalClassifyingHomotopyEquiv N k).invFun =
      (classifyingSpaceMap (evaluateHorizontalZero N k)).hom := rfl
end Realization
end CategoryTheory.Waldhausen.Fibration.MixedNerves
