/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.DiagonalEvaluation
public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.PostcomposeNerves

/-! # Prescribed evaluation in the original mixed-chain presentation

The accepted literal transpose transports original diagonal evaluation to
original coarse chains. Its exact forward map is a genuine realization
homotopy equivalence. Naturality retains actual compatible base functors;
the diagonal arrow comparison uses their proved composition law.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/ChainEvaluation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
variable {C : Type (max u v)} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The actual original mixed chain is evaluated along its diagonal. -/
def coarseChainEvaluation : SSet.diagonalSSet (coarseChainNerve N) ⟶
    nerve (TrivialCofibrations.WeakCategory N.coarse.weq) :=
  (coarseDiagonalIso N).hom ≫ diagonalEvaluation N

@[simp] theorem coarseChainEvaluation_obj (k : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N k) k.len) (i : Fin (k.len + 1)) :
    (((coarseChainEvaluation N).app (op k) F).obj i).obj = (F.obj i).obj.obj.obj i := rfl

/-- The exact original coarse arrow is followed by the original fine component. -/
@[simp] theorem coarseChainEvaluation_map (k : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N k) k.len) {i j : Fin (k.len + 1)} (f : i ⟶ j) :
    (((coarseChainEvaluation N).app (op k) F).map f).hom =
      (F.obj i).obj.obj.map f ≫ (F.map f).hom.hom.app j := rfl

/-- The prescribed original mixed-chain evaluation is a genuine realization equivalence. -/
def coarseChainEvaluationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (coarseChainNerve N)|
      (ClassifyingSpace (TrivialCofibrations.WeakCategory N.coarse.weq)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (coarseDiagonalIso N))).toHomotopyEquiv.trans
    (diagonalEvaluationHomotopyEquiv N)

@[simp] theorem coarseChainEvaluationHomotopyEquiv_toFun :
    (coarseChainEvaluationHomotopyEquiv N).toFun =
      (SSet.toTop.map (coarseChainEvaluation N)).hom := by
  simp only [coarseChainEvaluationHomotopyEquiv, coarseChainEvaluation, Functor.map_comp]
  rfl

/-- The original constant section, transported through the literal inverse transpose. -/
def coarseChainSection : nerve (TrivialCofibrations.WeakCategory N.coarse.weq) ⟶
    SSet.diagonalSSet (coarseChainNerve N) :=
  constantHorizontalDiagonalMap N ≫ (coarseDiagonalIso N).inv

@[simp] theorem coarseChainSection_evaluation :
    coarseChainSection N ≫ coarseChainEvaluation N = 𝟙 _ := by
  simp [coarseChainSection, coarseChainEvaluation, Category.assoc]

@[simp] theorem coarseChainEvaluationHomotopyEquiv_invFun :
    (coarseChainEvaluationHomotopyEquiv N).invFun =
      (SSet.toTop.map (coarseChainSection N)).hom := by
  change (SSet.toTop.map (coarseDiagonalIso N).inv).hom.comp
    (diagonalEvaluationHomotopyEquiv N).invFun = _
  rw [diagonalEvaluationHomotopyEquiv_invFun]
  rw [coarseChainSection, SSet.toTop.map_comp, TopCat.hom_comp]

/-- The actual cofibration-chain augmentation simply forgets the original cofibration witness. -/
def cofChainEvaluation : SSet.diagonalSSet (cofChainNerve N) ⟶
    nerve (TrivialCofibrations.WeakCategory N.coarse.weq) :=
  SSet.diagonalMap (chainInclusion N) ≫ coarseChainEvaluation N

section Naturality
variable {D : Type (max u v)} [Category.{v} D] {W : Structure D}
  {N} {M : NestedWeakEquivalences W} (F : CompatibleFunctor N M)

/-- The original base functor restricted to its actual coarse weak arrows. -/
def coarseWeakPostcompose : TrivialCofibrations.WeakCategory N.coarse.weq ⥤
    TrivialCofibrations.WeakCategory M.coarse.weq :=
  widePostcompose F.toFunctor _ _ (fun f hf ↦ F.coarse f hf)

/-- The original diagonal evaluation is strictly natural under actual base postcomposition. -/
theorem diagonalEvaluation_naturality :
    SSet.diagonalMap (horizontalNerveMap F) ≫ diagonalEvaluation M =
      diagonalEvaluation N ≫ nerveMap (coarseWeakPostcompose F) := by
  ext k G : 4
  change diagonalCoarseChain M k.unop (G ⋙ horizontalPostcompose F k.unop) =
    diagonalCoarseChain N k.unop G ⋙ coarseWeakPostcompose F
  refine CategoryTheory.Functor.ext
    (F := diagonalCoarseChain M k.unop (G ⋙ horizontalPostcompose F k.unop))
    (G := diagonalCoarseChain N k.unop G ⋙ coarseWeakPostcompose F) (fun _ ↦ rfl) ?_
  intro i j f
  apply WideSubcategory.hom_ext
  change F.toFunctor.map ((G.map f).hom.hom.app i) ≫
    F.toFunctor.map ((G.obj j).obj.obj.map f) =
      𝟙 _ ≫ F.toFunctor.map ((G.map f).hom.hom.app i ≫ (G.obj j).obj.obj.map f) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp]

/-- The same strict original-map naturality in the original coarse-chain presentation. -/
theorem coarseChainEvaluation_naturality :
    SSet.diagonalMap (coarseNerveMap F) ≫ coarseChainEvaluation M =
      coarseChainEvaluation N ≫ nerveMap (coarseWeakPostcompose F) := by
  simp only [coarseChainEvaluation, ← Category.assoc]
  rw [coarseDiagonalIso_naturality F]
  simp only [Category.assoc]
  rw [diagonalEvaluation_naturality F]

/-- The original cofibration-chain augmentation has the same strict target map. -/
theorem cofChainEvaluation_naturality :
    SSet.diagonalMap (cofNerveMap F) ≫ cofChainEvaluation M =
      cofChainEvaluation N ≫ nerveMap (coarseWeakPostcompose F) := by
  have h := congrArg SSet.diagonalMap (chainInclusion_naturality F)
  change SSet.diagonalMap (chainInclusion N) ≫ SSet.diagonalMap (coarseNerveMap F) =
    SSet.diagonalMap (cofNerveMap F) ≫ SSet.diagonalMap (chainInclusion M) at h
  simp only [cofChainEvaluation, ← Category.assoc]
  rw [← h]
  simp only [Category.assoc]
  rw [coarseChainEvaluation_naturality F]
end Naturality
end CategoryTheory.Waldhausen.Fibration.MixedNerves
