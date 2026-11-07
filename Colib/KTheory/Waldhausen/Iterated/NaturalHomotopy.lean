/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.Prespectrum
public import Colib.KTheory.Waldhausen.WeakNaturalTransformationBased

/-! Actual weak natural-transformation cylinders at every iterated S-stage. Their realized
homotopies retain the whole original basepoint track. -/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/NaturalHomotopy.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete based tracks,
structure-map parameters and universe assumptions are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u v u' v'
namespace CategoryTheory.Waldhausen

lemma mk₁_whiskerRight_spectrum {K C D : Type*} [Category* K] [Category* C] [Category* D]
    {A B : K ⥤ C} (η : A ⟶ B) (F : C ⥤ D) :
    ComposableArrows.mk₁ (whiskerRight η F) =
      ComposableArrows.mk₁ η ⋙ (whiskeringRight K C D).obj F := by
  apply ComposableArrows.ext₁ (F := ComposableArrows.mk₁ (whiskerRight η F))
    (G := ComposableArrows.mk₁ η ⋙ (whiskeringRight K C D).obj F) rfl rfl
  simp

lemma iteratedNerveCylinderDiagram_postcomp {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {n m : SimplexCategory}
    {A B : Grid₂ n m ⥤ C} (η : A ⟶ B) (F : C ⥤ D) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (whiskerRight η F) τ = nerveCylinderDiagram η τ ⋙ F := by
  unfold nerveCylinderDiagram
  rw [mk₁_whiskerRight_spectrum]
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp [Functor.uncurry, Functor.map_comp]

namespace IteratedS

open SmallWaldhausenCategory SSet Topology
variable {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}

/-- The genuine pointwise transformation on quotient rows. -/
def rowsTransformation (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (n : SimplexCategory) :
    ((rows n).map F).hom.toFunctor ⟶ ((rows n).map G).hom.toFunctor where
  app A := ObjectProperty.homMk (whiskerLeft A.obj η)
  naturality A B f := by
    apply ObjectProperty.hom_ext
    ext p
    exact η.naturality (f.hom.app p)

lemma rowsTransformation_weak (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (n : SimplexCategory)
    (A : ((rows n).obj V).obj.Obj) :
    ((rows n).obj W).obj.waldhausen.weq ((rowsTransformation η n).app A) := by
  intro p
  exact hη (A.obj.obj p)

/-- The actual nerve-parameter interpolation at each iterated S-simplex. -/
def stageTransformationFunction (r : ℕ) :
    {V W : WideSubcategory preservesZero.{u}} → {F G : V ⟶ W} →
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) → (∀ A, W.obj.waldhausen.weq (η.app A)) →
    (n : SimplexCategoryᵒᵖ) → ((stages r).obj V).obj n → (Δ[1]).obj n →
      ((stages r).obj W).obj n := by
  induction r with
  | zero =>
    intro V W F G η hη n A τ
    exact (weakNaturalTransformationCylinder V.obj.waldhausen W.obj.waldhausen
      F.hom.isExact G.hom.isExact η hη).app n (A, τ)
  | succ r ih =>
    intro V W F G η hη n A τ
    exact ih (rowsTransformation η n.unop)
      (rowsTransformation_weak η hη n.unop) n A τ

lemma stageTransformationFunction_postcomp (r : ℕ)
    {V W T : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (J : W ⟶ T)
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) :
    stageTransformationFunction r (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.hom.toFunctor) (fun A ↦ J.hom.isExact.weak _ (hη A)) n A τ =
      ((stages r).map J).app n (stageTransformationFunction r η hη n A τ) := by
  induction r generalizing V W T with
  | zero =>
    apply Subtype.ext
    exact iteratedNerveCylinderDiagram_postcomp (whiskerLeft A.val η) J.hom.toFunctor τ.down
  | succ r ih =>
    exact ih (rowsTransformation η n.unop) (rowsTransformation_weak η hη n.unop)
      ((rows n.unop).map J) A

lemma stageTransformationFunction_precomp (r : ℕ)
    {V W T : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (J : T ⟶ V)
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj T).obj n) (τ : (Δ[1]).obj n) :
    stageTransformationFunction r (F := J ≫ F) (G := J ≫ G)
      (whiskerLeft J.hom.toFunctor η) (fun A ↦ hη (J.hom.toFunctor.obj A)) n A τ =
      stageTransformationFunction r η hη n (((stages r).map J).app n A) τ := by
  induction r generalizing V W T with
  | zero => rfl
  | succ r ih =>
    exact ih (rowsTransformation η n.unop) (rowsTransformation_weak η hη n.unop)
      ((rows n.unop).map J) A

lemma stageTransformationFunction_naturality (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) :
    ((stages r).obj W).map α (stageTransformationFunction r η hη n A τ) =
      stageTransformationFunction r η hη m (((stages r).obj V).map α A) ((Δ[1]).map α τ) := by
  induction r generalizing V W with
  | zero =>
    have h := congrArg (fun f ↦ f (A,τ))
      ((weakNaturalTransformationCylinder V.obj.waldhausen W.obj.waldhausen
        F.hom.isExact G.hom.isExact η hη).naturality α)
    exact h.symm
  | succ r ih =>
    change ((stages r).obj ((rows m.unop).obj W)).map α
      (((stages r).map ((rowsReindex α.unop).app W)).app n
        (stageTransformationFunction r (rowsTransformation η n.unop)
          (rowsTransformation_weak η hη n.unop) n A τ)) = _
    rw [← stageTransformationFunction_postcomp]
    rw [ih]
    change stageTransformationFunction r
      (F := (rowsReindex α.unop).app V ≫ (rows m.unop).map F)
      (G := (rowsReindex α.unop).app V ≫ (rows m.unop).map G)
      (whiskerLeft ((rowsReindex α.unop).app V).hom.toFunctor (rowsTransformation η m.unop))
      (fun B ↦ rowsTransformation_weak η hη m.unop
        (((rowsReindex α.unop).app V).hom.toFunctor.obj B))
      m (((stages r).obj ((rows n.unop).obj V)).map α A) ((Δ[1]).map α τ) = _
    rw [stageTransformationFunction_precomp]
    congr 1
    exact ConcreteCategory.congr_hom
      (((stages r).map ((rowsReindex α.unop).app V)).naturality α) A

/-- Pointwise weak exact-functor transformations give a genuine simplicial
cylinder at every original iterated stage. -/
def stageTransformationCylinder (r : ℕ) {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) :
    (stages r).obj V ⊗ Δ[1] ⟶ (stages r).obj W where
  app n := ↾fun z ↦ stageTransformationFunction r η hη n z.1 z.2
  naturality n m α := by
    ext z : 3
    exact (stageTransformationFunction_naturality r η hη α z.1 z.2).symm

lemma stageTransformationFunction_zero (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) :
    stageTransformationFunction r η hη n A ⟨n.unop.const ⦋1⦌ 0⟩ =
      ((stages r).map F).app n A := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveCylinderDiagram_zero (whiskerLeft A.val η)
  | succ r ih =>
    exact ih (rowsTransformation η n.unop) (rowsTransformation_weak η hη n.unop) A

lemma stageTransformationFunction_one (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) :
    stageTransformationFunction r η hη n A ⟨n.unop.const ⦋1⦌ 1⟩ =
      ((stages r).map G).app n A := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveCylinderDiagram_one (whiskerLeft A.val η)
  | succ r ih =>
    exact ih (rowsTransformation η n.unop) (rowsTransformation_weak η hη n.unop) A

/-- The iterated-stage simplicial homotopy induced by an objectwise weak natural transformation. -/
def stageTransformationHomotopy (r : ℕ) {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) :
    SSet.Homotopy ((stages r).map F) ((stages r).map G) where
  h := stageTransformationCylinder r η hη
  h₀ := by ext n A : 4; exact stageTransformationFunction_zero r η hη n A
  h₁ := by ext n A : 4; exact stageTransformationFunction_one r η hη n A
  rel := by ext n z; exact z.1.property.elim

/-- The degenerate simplex obtained from the iterated-stage zero vertex. -/
def stageZeroSimplex (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n : SimplexCategoryᵒᵖ) :
    ((stages r).obj W).obj n :=
  ((stages r).obj W).map (n.unop.const ⦋0⦌ 0).op (stageVertex r W)

lemma stageZeroSimplex_succ (r : ℕ) (W : WideSubcategory preservesZero.{u})
    (n : SimplexCategoryᵒᵖ) :
    stageZeroSimplex (r+1) W n = stageZeroSimplex r ((rows n.unop).obj W) n := by
  change ((stages r).obj ((rows n.unop).obj W)).map (n.unop.const ⦋0⦌ 0).op
    (((stages r).map ((rowsReindex (n.unop.const ⦋0⦌ 0)).app W)).app (op ⦋0⦌)
      (stageVertex r ((rows ⦋0⦌).obj W))) = _
  rw [stageVertex_naturality]
  rfl

lemma stageTransformationFunction_zeroSimplex (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (n : SimplexCategoryᵒᵖ) (τ : (Δ[1]).obj n) :
    stageTransformationFunction r η hη n (stageZeroSimplex r V n) τ =
      stageZeroSimplex r W n := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveCylinderDiagram_eq_const_of_zero _ W.obj.waldhausen.zero W.obj.waldhausen.isZero
      (fun _ ↦ show F.hom.toFunctor.obj V.obj.waldhausen.zero = W.obj.waldhausen.zero from
        F.property) (fun _ ↦ show G.hom.toFunctor.obj V.obj.waldhausen.zero =
        W.obj.waldhausen.zero from G.property) τ.down
  | succ r ih =>
    rw [stageZeroSimplex_succ, stageZeroSimplex_succ]
    exact ih (rowsTransformation η n.unop) (rowsTransformation_weak η hη n.unop)

lemma stageTransformationCylinder_fixed_vertex (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) :
    SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[1] ≫ stageTransformationCylinder r η hη =
      CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (stageVertex r W) := by
  ext n z : 4
  change stageTransformationFunction r η hη n
    (((stages r).obj V).map z.1.down.op (stageVertex r V)) z.2 =
      ((stages r).obj W).map z.1.down.op (stageVertex r W)
  have hz : z.1.down = n.unop.const ⦋0⦌ 0 :=
    @Subsingleton.elim (n.unop ⟶ ⦋0⦌) inferInstance _ _
  rw [hz]
  exact stageTransformationFunction_zeroSimplex r η hη n z.2

/-- Every original iterated S-map admits the actual realized based homotopy. -/
def stageTransformationTopHomotopy (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) :
    (SSet.toTop.map ((stages r).map F)).hom.Homotopy
      (SSet.toTop.map ((stages r).map G)).hom :=
  realizationSimplicialHomotopy (stageTransformationHomotopy r η hη)

lemma stageTransformationTopHomotopy_fixed_point (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (t : unitInterval) :
    stageTransformationTopHomotopy r η hη (t, stagePoint r V) = stagePoint r W :=
  realizationSimplicialHomotopy_fixed_vertex (stageTransformationHomotopy r η hη)
    (stageVertex r V) (stageVertex r W) (stageTransformationCylinder_fixed_vertex r η hη) t

end IteratedS
end CategoryTheory.Waldhausen
