/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.ConstantDiagonal

/-! # The prescribed original diagonal evaluation

The actual double diagram is evaluated at its diagonal vertices and arrows.
The horizontal map is coarse weak and the vertical fine map is coarse weak
by nesting, so their original composite is a coarse weak arrow. This defines
a genuine simplicial map, strictly retracting the original constant-chain
inclusion. Its realization has that prescribed evaluation as forward map.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/DiagonalEvaluation.lean`
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
section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Each original fine chain is regarded as a coarse chain; horizontal maps
retain their original pointwise coarse witnesses. -/
def horizontalCoarseDiagram (k : SimplexCategory) : HorizontalChains N k ⥤
    ComposableArrows (TrivialCofibrations.WeakCategory N.coarse.weq) k.len where
  obj F := {
    obj i := ⟨F.obj.obj.obj i⟩
    map f := ⟨F.obj.obj.map f, N.le_weq _ (F.obj.property f)⟩
    map_id i := WideSubcategory.hom_ext _ (F.obj.obj.map_id i)
    map_comp f g := WideSubcategory.hom_ext _ (F.obj.obj.map_comp f g) }
  map f := {
    app i := ⟨f.hom.hom.app i, f.property i⟩
    naturality _ _ g := WideSubcategory.hom_ext _ (f.hom.hom.naturality g) }
  map_id _ := by ext i; rfl
  map_comp _ _ := by ext i; rfl

/-- The original double diagram is restricted along the actual diagonal functor. -/
def diagonalCoarseChain (k : SimplexCategory)
    (F : ComposableArrows (HorizontalChains N k) k.len) :
    ComposableArrows (TrivialCofibrations.WeakCategory N.coarse.weq) k.len :=
  Functor.diag _ ⋙ Functor.uncurry.obj (F ⋙ horizontalCoarseDiagram N k)

@[simp] theorem diagonalCoarseChain_obj (k : SimplexCategory)
    (F : ComposableArrows (HorizontalChains N k) k.len) (i : Fin (k.len + 1)) :
    ((diagonalCoarseChain N k F).obj i).obj = (F.obj i).obj.obj.obj i := rfl

/-- The arrow is the original horizontal component followed by the original fine arrow. -/
@[simp] theorem diagonalCoarseChain_map (k : SimplexCategory)
    (F : ComposableArrows (HorizontalChains N k) k.len) {i j : Fin (k.len + 1)} (f : i ⟶ j) :
    ((diagonalCoarseChain N k F).map f).hom =
      (F.map f).hom.hom.app i ≫ (F.obj j).obj.obj.map f := rfl

/-- The displayed original composite is genuinely coarse weak. -/
theorem diagonalCoarseChain_map_weak (k : SimplexCategory)
    (F : ComposableArrows (HorizontalChains N k) k.len) {i j : Fin (k.len + 1)} (f : i ⟶ j) :
    N.coarse.weq ((F.map f).hom.hom.app i ≫ (F.obj j).obj.obj.map f) :=
  ((diagonalCoarseChain N k F).map f).property
end Categorical

section Realization
variable {C : Type (max u v)} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Original diagonal evaluation commutes with every original simplicial operator. -/
def diagonalEvaluation : SSet.diagonalSSet (horizontalNerve N) ⟶
    nerve (TrivialCofibrations.WeakCategory N.coarse.weq) where
  app k := ↾(diagonalCoarseChain N k.unop)
  naturality _ _ _ := by
    ext F : 3
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem diagonalEvaluation_app (k : SimplexCategory)
    (F : ComposableArrows (HorizontalChains N k) k.len) :
    (diagonalEvaluation N).app (op k) F = diagonalCoarseChain N k F := rfl

/-- The actual constant-chain inclusion is a strict simplicial section of evaluation. -/
@[simp] theorem constantDiagonal_evaluation :
    constantHorizontalDiagonalMap N ≫ diagonalEvaluation N = 𝟙 _ := by
  ext k F : 4
  change diagonalCoarseChain N k.unop (F ⋙ constantHorizontal N k.unop) = F
  refine CategoryTheory.Functor.ext (F := diagonalCoarseChain N k.unop
    (F ⋙ constantHorizontal N k.unop)) (G := F) (fun _ ↦ rfl) ?_
  intro i j f
  apply WideSubcategory.hom_ext
  change (F.map f).hom ≫ 𝟙 _ = 𝟙 _ ≫ (F.map f).hom ≫ 𝟙 _
  simp

/-- Realization retains the actual strict section equality. -/
theorem diagonalEvaluation_constant :
    (SSet.toTop.map (diagonalEvaluation N)).hom.comp
      (SSet.toTop.map (constantHorizontalDiagonalMap N)).hom = ContinuousMap.id _ := by
  have h := congrArg (fun f ↦ (SSet.toTop.map f).hom) (constantDiagonal_evaluation N)
  rw [SSet.toTop.map_comp, TopCat.hom_comp, SSet.toTop.map_id, TopCat.hom_id] at h
  exact h

/-- Evaluation itself is the prescribed forward homotopy equivalence, with
its inverse exactly the original constant-chain inclusion. -/
def diagonalEvaluationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (horizontalNerve N)|
      (ClassifyingSpace (TrivialCofibrations.WeakCategory N.coarse.weq)) := by
  let E := constantHorizontalDiagonalHomotopyEquiv N
  let p := (SSet.toTop.map (diagonalEvaluation N)).hom
  have hs : p.comp E.toFun = ContinuousMap.id _ := by
    dsimp [p, E]
    rw [constantHorizontalDiagonalHomotopyEquiv_toFun]
    exact diagonalEvaluation_constant N
  have hp : p.Homotopic E.invFun := by
    have h := (ContinuousMap.Homotopic.refl p).comp E.right_inv
    change ((p.comp E.toFun).comp E.invFun).Homotopic p at h
    rw [hs, ContinuousMap.id_comp] at h
    exact h.symm
  exact {
    toFun := p
    invFun := E.toFun
    left_inv := ((ContinuousMap.Homotopic.refl E.toFun).comp hp).trans E.right_inv
    right_inv := by rw [hs] }

@[simp] theorem diagonalEvaluationHomotopyEquiv_toFun :
    (diagonalEvaluationHomotopyEquiv N).toFun =
      (SSet.toTop.map (diagonalEvaluation N)).hom := rfl

@[simp] theorem diagonalEvaluationHomotopyEquiv_invFun :
    (diagonalEvaluationHomotopyEquiv N).invFun =
      (SSet.toTop.map (constantHorizontalDiagonalMap N)).hom :=
  constantHorizontalDiagonalHomotopyEquiv_toFun N
end Realization
end CategoryTheory.Waldhausen.Fibration.MixedNerves
