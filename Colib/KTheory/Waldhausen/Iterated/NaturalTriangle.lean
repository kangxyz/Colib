/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationTriangle
public import Colib.KTheory.Waldhausen.Iterated.NaturalHomotopy

/-! # Actual triangles at every iterated S-stage

The original two weak transformations are propagated through quotient rows. The resulting Δ[2]
family retains all three original transformation-cylinder faces and the complete zero triangle.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/NaturalTriangle.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, simplex faces,
whole fixed-zero family, and independent structure parameters are retained under native ownership.
  -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe u v u' v'

namespace CategoryTheory.Waldhausen

private lemma mk₂_whiskerRight_triangle {K C D : Type*} [Category* K] [Category* C] [Category* D]
    {A B C' : K ⥤ C} (η : A ⟶ B) (θ : B ⟶ C') (F : C ⥤ D) :
    ComposableArrows.mk₂ (whiskerRight η F) (whiskerRight θ F) =
      ComposableArrows.mk₂ η θ ⋙ (whiskeringRight K C D).obj F := by
  apply ComposableArrows.ext₂
    (f := ComposableArrows.mk₂ (whiskerRight η F) (whiskerRight θ F))
    (g := ComposableArrows.mk₂ η θ ⋙ (whiskeringRight K C D).obj F) rfl rfl rfl <;> simp

/-- Postcomposition retains the entire original nerve-triangle diagram. -/
lemma iteratedNerveTriangleDiagram_postcomp {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {n m : SimplexCategory}
    {A B C' : Grid₂ n m ⥤ C} (η : A ⟶ B) (θ : B ⟶ C') (F : C ⥤ D) (τ : m ⟶ ⦋2⦌) :
    nerveTriangleDiagram (whiskerRight η F) (whiskerRight θ F) τ =
      nerveTriangleDiagram η θ τ ⋙ F := by
  unfold nerveTriangleDiagram
  rw [mk₂_whiskerRight_triangle]
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp [Functor.uncurry, Functor.map_comp]

namespace IteratedS

open SmallWaldhausenCategory SSet Topology

/-- The actual two-arrow nerve interpolation at each original iterated S-simplex. -/
def stageTriangleFunction (r : ℕ) :
    {V W : WideSubcategory preservesZero.{u}} → {F G H : V ⟶ W} →
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) → (θ : G.hom.toFunctor ⟶ H.hom.toFunctor) →
    (∀ A, W.obj.waldhausen.weq (η.app A)) → (∀ A, W.obj.waldhausen.weq (θ.app A)) →
    (n : SimplexCategoryᵒᵖ) → ((stages r).obj V).obj n → (Δ[2]).obj n →
      ((stages r).obj W).obj n := by
  induction r with
  | zero =>
    intro V W F G H η θ hη hθ n A τ
    exact (weakNaturalTransformationTriangle V.obj.waldhausen W.obj.waldhausen
      F.hom.isExact G.hom.isExact H.hom.isExact η θ hη hθ).app n (A, τ)
  | succ r ih =>
    intro V W F G H η θ hη hθ n A τ
    exact ih (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop) n A τ

lemma stageTriangleFunction_postcomp (r : ℕ)
    {V W T : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (J : W ⟶ T) (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ : (Δ[2]).obj n) :
    stageTriangleFunction r (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
      (whiskerRight η J.hom.toFunctor) (whiskerRight θ J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) (fun A ↦ J.hom.isExact.weak _ (hθ A)) n A τ =
      ((stages r).map J).app n (stageTriangleFunction r η θ hη hθ n A τ) := by
  induction r generalizing V W T with
  | zero =>
    apply Subtype.ext
    exact iteratedNerveTriangleDiagram_postcomp
      (whiskerLeft A.val η) (whiskerLeft A.val θ) J.hom.toFunctor τ.down
  | succ r ih =>
    exact ih (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop)
      ((rows n.unop).map J) A

lemma stageTriangleFunction_precomp (r : ℕ)
    {V W T : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (J : T ⟶ V) (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj T).obj n) (τ : (Δ[2]).obj n) :
    stageTriangleFunction r (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
      (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hθ (J.hom.toFunctor.obj A)) n A τ =
      stageTriangleFunction r η θ hη hθ n (((stages r).map J).app n A) τ := by
  induction r generalizing V W T with
  | zero => rfl
  | succ r ih =>
    exact ih (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop)
      ((rows n.unop).map J) A

lemma stageTriangleFunction_naturality (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (A : ((stages r).obj V).obj n) (τ : (Δ[2]).obj n) :
    ((stages r).obj W).map α (stageTriangleFunction r η θ hη hθ n A τ) =
      stageTriangleFunction r η θ hη hθ m (((stages r).obj V).map α A) ((Δ[2]).map α τ) := by
  induction r generalizing V W with
  | zero =>
    have h := congrArg (fun f ↦ f (A, τ))
      ((weakNaturalTransformationTriangle V.obj.waldhausen W.obj.waldhausen
        F.hom.isExact G.hom.isExact H.hom.isExact η θ hη hθ).naturality α)
    exact h.symm
  | succ r ih =>
    change ((stages r).obj ((rows m.unop).obj W)).map α
      (((stages r).map ((rowsReindex α.unop).app W)).app n
        (stageTriangleFunction r (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
          (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop) n A τ)) = _
    rw [← stageTriangleFunction_postcomp, ih]
    change stageTriangleFunction r
      (F := (rowsReindex α.unop).app V ≫ (rows m.unop).map F)
      (G := (rowsReindex α.unop).app V ≫ (rows m.unop).map G)
      (H := (rowsReindex α.unop).app V ≫ (rows m.unop).map H)
      (whiskerLeft ((rowsReindex α.unop).app V).hom.toFunctor (rowsTransformation η m.unop))
      (whiskerLeft ((rowsReindex α.unop).app V).hom.toFunctor (rowsTransformation θ m.unop))
      (fun B ↦ rowsTransformation_weak η hη m.unop
        (((rowsReindex α.unop).app V).hom.toFunctor.obj B))
      (fun B ↦ rowsTransformation_weak θ hθ m.unop
        (((rowsReindex α.unop).app V).hom.toFunctor.obj B))
      m (((stages r).obj ((rows n.unop).obj V)).map α A) ((Δ[2]).map α τ) = _
    rw [stageTriangleFunction_precomp]
    congr 1
    exact ConcreteCategory.congr_hom
      (((stages r).map ((rowsReindex α.unop).app V)).naturality α) A

/-- The genuine simplicial triangle at every iterated stage. -/
def stageTransformationTriangle (r : ℕ) {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A)) :
    (stages r).obj V ⊗ Δ[2] ⟶ (stages r).obj W where
  app n := ↾fun z ↦ stageTriangleFunction r η θ hη hθ n z.1 z.2
  naturality n m α := by
    ext z : 3
    exact (stageTriangleFunction_naturality r η θ hη hθ α z.1 z.2).symm

variable {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
  (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))

lemma stageTriangleFunction_first (r : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) :
    stageTriangleFunction r η θ hη hθ n A ⟨τ.down ≫ SimplexCategory.δ 2⟩ =
      stageTransformationFunction r η hη n A τ := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveTriangleDiagram_first (whiskerLeft A.val η) (whiskerLeft A.val θ) τ.down
  | succ r ih =>
    exact ih (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop) A

/-- The first face is the original iterated transformation cylinder. -/
theorem stageTransformationTriangle_first (r : ℕ) :
    ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.δ 2) ≫
        stageTransformationTriangle r η θ hη hθ =
      stageTransformationCylinder r η hη := by
  ext n z : 4
  exact stageTriangleFunction_first η θ hη hθ r n z.1 z.2

lemma stageTriangleFunction_second (r : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) :
    stageTriangleFunction r η θ hη hθ n A ⟨τ.down ≫ SimplexCategory.δ 0⟩ =
      stageTransformationFunction r θ hθ n A τ := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveTriangleDiagram_second (whiskerLeft A.val η) (whiskerLeft A.val θ) τ.down
  | succ r ih =>
    exact ih (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop) A

/-- The second face is the original iterated transformation cylinder. -/
theorem stageTransformationTriangle_second (r : ℕ) :
    ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.δ 0) ≫
        stageTransformationTriangle r η θ hη hθ =
      stageTransformationCylinder r θ hθ := by
  ext n z : 4
  exact stageTriangleFunction_second η θ hη hθ r n z.1 z.2

lemma stageTriangleFunction_composite (r : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) :
    stageTriangleFunction r η θ hη hθ n A ⟨τ.down ≫ SimplexCategory.δ 1⟩ =
      stageTransformationFunction r (η ≫ θ)
        (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) n A τ := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveTriangleDiagram_composite (whiskerLeft A.val η) (whiskerLeft A.val θ) τ.down
  | succ r ih =>
    exact ih (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop) A

/-- The composite face is the original iterated transformation cylinder. -/
theorem stageTransformationTriangle_composite (r : ℕ) :
    ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.δ 1) ≫
        stageTransformationTriangle r η θ hη hθ =
      stageTransformationCylinder r (η ≫ θ)
        (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) := by
  ext n z : 4
  exact stageTriangleFunction_composite η θ hη hθ r n z.1 z.2

lemma stageTriangleFunction_zeroSimplex (r : ℕ)
    (n : SimplexCategoryᵒᵖ) (τ : (Δ[2]).obj n) :
    stageTriangleFunction r η θ hη hθ n (stageZeroSimplex r V n) τ =
      stageZeroSimplex r W n := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveTriangleDiagram_eq_const_of_zero _ _ W.obj.waldhausen.zero W.obj.waldhausen.isZero
      (fun _ ↦ show F.hom.toFunctor.obj V.obj.waldhausen.zero =
        W.obj.waldhausen.zero from F.property) (fun _ ↦ show G.hom.toFunctor.obj
          V.obj.waldhausen.zero =
        W.obj.waldhausen.zero from G.property) (fun _ ↦ show H.hom.toFunctor.obj
          V.obj.waldhausen.zero =
        W.obj.waldhausen.zero from H.property) τ.down
  | succ r ih =>
    rw [stageZeroSimplex_succ, stageZeroSimplex_succ]
    exact ih (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop)

/-- The whole original triangle stays at the iterated stage's actual chosen-zero vertex. -/
theorem stageTransformationTriangle_fixed_vertex (r : ℕ) :
    SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[2] ≫ stageTransformationTriangle r η θ hη hθ =
      CartesianMonoidalCategory.fst Δ[0] Δ[2] ≫ SSet.yonedaEquiv.symm (stageVertex r W) := by
  ext n z : 4
  change stageTriangleFunction r η θ hη hθ n
    (((stages r).obj V).map z.1.down.op (stageVertex r V)) z.2 =
      ((stages r).obj W).map z.1.down.op (stageVertex r W)
  have hz : z.1.down = n.unop.const ⦋0⦌ 0 :=
    @Subsingleton.elim (n.unop ⟶ ⦋0⦌) inferInstance _ _
  rw [hz]
  exact stageTriangleFunction_zeroSimplex η θ hη hθ r n z.2

end IteratedS
end CategoryTheory.Waldhausen
