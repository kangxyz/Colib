/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.ChainCategories

/-! # Literal postcomposition of the original mixed chain categories

Only preservation of the three original arrow predicates is used. Every
object and component map is the original functor's image. No realization
or comparison square is an input.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/Postcompose.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration.RelativeRows


noncomputable section
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
open RelativeRows
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {V : Structure C} {W : Structure D} {U : Structure E}

/-- An original functor preserving the fine, cofibration, and coarse arrow predicates. -/
structure CompatibleFunctor (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W) where
  /-- The underlying functor from `C` to `D`, required to preserve the fine weak equivalences,
  cofibrations, and coarse weak equivalences separately. -/
  toFunctor : C ⥤ D
  fine {X Y : C} (f : X ⟶ Y) : V.weq f → W.weq (toFunctor.map f)
  cof {X Y : C} (f : X ⟶ Y) : V.cof f → W.cof (toFunctor.map f)
  coarse {X Y : C} (f : X ⟶ Y) : N.coarse.weq f → M.coarse.weq (toFunctor.map f)

namespace CompatibleFunctor
variable (N : NestedWeakEquivalences V)
/-- The actual identity functor preserves all original arrow predicates. -/
def id : CompatibleFunctor N N where
  toFunctor := 𝟭 C
  fine _ h := h
  cof _ h := h
  coarse _ h := h
variable {N} {M : NestedWeakEquivalences W} {L : NestedWeakEquivalences U}
/-- Actual composition retains preservation of all three arrow predicates. -/
def comp (F : CompatibleFunctor N M) (G : CompatibleFunctor M L) : CompatibleFunctor N L where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  fine f h := G.fine _ (F.fine f h)
  cof f h := G.cof _ (F.cof f h)
  coarse f h := G.coarse _ (F.coarse f h)
end CompatibleFunctor

/-- Restrict literal diagram postcomposition to the proved original object predicates. -/
def chainPostcompose (F : C ⥤ D) (n : SimplexCategory)
    (S : ObjectProperty (ComposableArrows C n.len))
    (T : ObjectProperty (ComposableArrows D n.len))
    (h : ∀ X, S X → T (X ⋙ F)) : S.FullSubcategory ⥤ T.FullSubcategory :=
  T.lift (S.ι ⋙ (Functor.whiskeringRight (Fin (n.len+1)) C D).obj F)
    (fun X ↦ h X.obj X.property)

/-- Restrict the unchanged original functor to original arrows satisfying the predicates. -/
def widePostcompose (F : C ⥤ D) (P : MorphismProperty C) (Q : MorphismProperty D)
    [P.IsMultiplicative] [Q.IsMultiplicative]
    (h : ∀ {X Y} (f : X ⟶ Y), P f → Q (F.map f)) : WideSubcategory P ⥤ WideSubcategory Q where
  obj X := ⟨F.obj X.obj⟩
  map f := ⟨F.map f.hom, h f.hom f.property⟩
  map_id X := WideSubcategory.hom_ext _ (F.map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext _ (F.map_comp f.hom g.hom)

variable {N : NestedWeakEquivalences V} {M : NestedWeakEquivalences W}
  (F : CompatibleFunctor N M)

/-- Literal postcomposition of fine-weak chains, still retaining every natural transformation. -/
def finePostcompose (k : SimplexCategory) : FineChain V k ⥤ FineChain W k :=
  chainPostcompose F.toFunctor k (fineChains V k) (fineChains W k)
    (fun _ h ↦ by intro _ _ f; exact F.fine _ (h f))
/-- Literal postcomposition of the accepted original coarse-weak chains. -/
def coarsePostcompose (n : SimplexCategory) : CoarseWeakChain N n ⥤ CoarseWeakChain M n :=
  chainPostcompose F.toFunctor n (coarseWeakChains N n) (coarseWeakChains M n)
    (fun _ h ↦ by intro _ _ f; exact F.coarse _ (h f))
/-- Literal postcomposition preserves both original cofibration-chain predicates. -/
def cofPostcompose (n : SimplexCategory) : CofibrationWeakChain N n ⥤ CofibrationWeakChain M n :=
  chainPostcompose F.toFunctor n (cofibrationWeakChains N n) (cofibrationWeakChains M n)
    (fun _ h ↦ ⟨fun f ↦ F.cof _ (h.1 f), fun f ↦ F.coarse _ (h.2 f)⟩)

/-- Original pointwise fine maps of original coarse chains are mapped componentwise. -/
def fineWeakCoarsePostcompose (n : SimplexCategory) :
    FineWeakCoarseChains N n ⥤ FineWeakCoarseChains M n :=
  widePostcompose (coarsePostcompose F n) _ _ (fun _f hf i ↦ F.fine _ (hf i))
/-- The same actual fine maps retain the original cofibration object condition. -/
def fineWeakCofPostcompose (n : SimplexCategory) : FineWeakChains N n ⥤ FineWeakChains M n :=
  widePostcompose (cofPostcompose F n) _ _ (fun _f hf i ↦ F.fine _ (hf i))
/-- Original coarse transformations between fine chains are mapped componentwise. -/
def horizontalPostcompose (k : SimplexCategory) : HorizontalChains N k ⥤ HorizontalChains M k :=
  widePostcompose (finePostcompose F k) _ _ (fun _f hf i ↦ F.coarse _ (hf i))
/-- Original weak cofibration transformations are mapped by the same component functor. -/
def horizontalCofPostcompose (k : SimplexCategory) :
    HorizontalCofChains N k ⥤ HorizontalCofChains M k :=
  widePostcompose (finePostcompose F k) _ _
    (fun _f hf ↦ ⟨fun i ↦ F.cof _ (hf.1 i), fun i ↦ F.coarse _ (hf.2 i)⟩)

@[simp] theorem finePostcompose_obj (k : SimplexCategory) (X : FineChain V k) :
    ((finePostcompose F k).obj X).obj = X.obj ⋙ F.toFunctor := rfl
@[simp] theorem finePostcompose_map_app (k : SimplexCategory) {X Y : FineChain V k}
    (f : X ⟶ Y) (i : Fin (k.len + 1)) :
    ((finePostcompose F k).map f).hom.app i = F.toFunctor.map (f.hom.app i) := rfl
@[simp] theorem fineWeakCoarsePostcompose_obj (n : SimplexCategory) (X : FineWeakCoarseChains N n) :
    ((fineWeakCoarsePostcompose F n).obj X).obj.obj = X.obj.obj ⋙ F.toFunctor := rfl
@[simp] theorem fineWeakCoarsePostcompose_map_app (n : SimplexCategory)
    {X Y : FineWeakCoarseChains N n} (f : X ⟶ Y) (i : Fin (n.len + 1)) :
    ((fineWeakCoarsePostcompose F n).map f).hom.hom.app i = F.toFunctor.map (f.hom.hom.app i) := rfl
@[simp] theorem horizontalPostcompose_map_app (k : SimplexCategory)
    {X Y : HorizontalChains N k} (f : X ⟶ Y) (i : Fin (k.len + 1)) :
    ((horizontalPostcompose F k).map f).hom.hom.app i = F.toFunctor.map (f.hom.hom.app i) := rfl

/-- Actual coarse-index restriction commutes strictly with literal postcomposition. -/
theorem fineWeakCoarsePostcompose_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    fineWeakCoarseReindex N α ⋙ fineWeakCoarsePostcompose F m =
      fineWeakCoarsePostcompose F n ⋙ fineWeakCoarseReindex M α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- The same strict equality retains the original cofibration predicates. -/
theorem fineWeakCofPostcompose_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    fineWeakCofReindex N α ⋙ fineWeakCofPostcompose F m =
      fineWeakCofPostcompose F n ⋙ fineWeakCofReindex M α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- Actual fine-index restriction commutes strictly with literal postcomposition. -/
theorem horizontalPostcompose_reindex {k l : SimplexCategory} (α : k ⟶ l) :
    horizontalReindex N α ⋙ horizontalPostcompose F k =
      horizontalPostcompose F l ⋙ horizontalReindex M α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- The same strict equality retains original horizontal weak cofibrations. -/
theorem horizontalCofPostcompose_reindex {k l : SimplexCategory} (α : k ⟶ l) :
    horizontalCofReindex N α ⋙ horizontalCofPostcompose F k =
      horizontalCofPostcompose F l ⋙ horizontalCofReindex M α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The unchanged original inclusion commutes strictly with the base functor. -/
theorem weakForgetCofChain_postcompose (n : SimplexCategory) :
    weakForgetCofChain N n ⋙ fineWeakCoarsePostcompose F n =
      fineWeakCofPostcompose F n ⋙ weakForgetCofChain M n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- The unchanged transposed inclusion commutes strictly with the same base functor. -/
theorem horizontalInclusion_postcompose (k : SimplexCategory) :
    horizontalInclusion N k ⋙ horizontalPostcompose F k =
      horizontalCofPostcompose F k ⋙ horizontalInclusion M k := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.MixedNerves
