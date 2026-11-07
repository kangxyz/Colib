/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.NaturalHomotopy
public import Colib.Topology.Realization.DoubleHomotopy

/-! The insertion square for genuine natural transformations, and compatibility of the complete
realized homotopies with every original spectrum structure map. -/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/StructureHomotopy.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete based tracks,
structure-map parameters and universe assumptions are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

lemma rowsTransformation_insertion_square {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    whiskerRight η ((insertion τ).app W).hom.toFunctor ≫
      eqToHom (congrArg (fun f ↦ f.hom.toFunctor) ((insertion τ).naturality G)) =
    eqToHom (congrArg (fun f ↦ f.hom.toFunctor) ((insertion τ).naturality F)) ≫
      whiskerLeft ((insertion τ).app V).hom.toFunctor (rowsTransformation η n) := by
  ext A : 2
  simp only [NatTrans.comp_app, eqToHom_app]
  apply (QuotientRows.objects W.obj.waldhausen n).ι.map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  ext p
  simp only [NatTrans.comp_app, eqToHom_app, whiskerRight_app, whiskerLeft_app]
  change ((suspensionRow W.obj.waldhausen τ).map (η.app A)).hom.app p ≫ eqToHom _ =
    eqToHom _ ≫ η.app (((suspensionRow V.obj.waldhausen τ).obj A).obj.obj p)
  have h (l : Fin 3)
      (eF : ((QuotientRows.oneChain W.obj.waldhausen).obj l).obj (F.hom.toFunctor.obj A) =
        F.hom.toFunctor.obj (((QuotientRows.oneChain V.obj.waldhausen).obj l).obj A))
      (eG : ((QuotientRows.oneChain W.obj.waldhausen).obj l).obj (G.hom.toFunctor.obj A) =
        G.hom.toFunctor.obj (((QuotientRows.oneChain V.obj.waldhausen).obj l).obj A)) :
      ((QuotientRows.oneChain W.obj.waldhausen).obj l).map (η.app A) ≫ eqToHom eG =
        eqToHom eF ≫ η.app (((QuotientRows.oneChain V.obj.waldhausen).obj l).obj A) := by
    fin_cases l
    · exact W.obj.waldhausen.isZero.eq_of_src _ _
    · simp [QuotientRows.oneChain, ComposableArrows.mk₂]
    · exact W.obj.waldhausen.isZero.eq_of_src _ _
  exact h (QuotientRows.oneIndex.obj ((QuotientRows.indexMap τ).obj p)) _ _

lemma stageTransformationFunction_congr (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {F G F' G' : V ⟶ W} (eF : F = F') (eG : G = G')
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (η' : F'.hom.toFunctor ⟶ G'.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq (η'.app A))
    (h : η ≫ eqToHom (congrArg (fun f ↦ f.hom.toFunctor) eG) =
      eqToHom (congrArg (fun f ↦ f.hom.toFunctor) eF) ≫ η')
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) :
    stageTransformationFunction r η hη n A τ = stageTransformationFunction r η' hη' n A τ := by
  cases eF
  cases eG
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
  subst η'
  rfl

lemma stageTransformationFunction_structure (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ θ : (Δ[1]).obj n) :
    stageTransformationFunction (r+1) η hη n ((stageCylinder r V).app n (A,τ)) θ =
      (stageCylinder r W).app n (stageTransformationFunction r η hη n A θ,τ) := by
  change stageTransformationFunction r (rowsTransformation η n.unop)
    (rowsTransformation_weak η hη n.unop) n
    (((stages r).map ((insertion τ.down).app V)).app n A) θ =
      ((stages r).map ((insertion τ.down).app W)).app n
        (stageTransformationFunction r η hη n A θ)
  rw [← stageTransformationFunction_precomp, ← stageTransformationFunction_postcomp]
  exact (stageTransformationFunction_congr r ((insertion τ.down).naturality F)
    ((insertion τ.down).naturality G) _ _ _ _
    (rowsTransformation_insertion_square η τ.down) n A θ).symm

lemma stageTransformationCylinder_structure (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) :
    stageCylinder r V ▷ Δ[1] ≫ stageTransformationCylinder (r+1) η hη =
      simplicialCylinderSwap ((stages r).obj V) ≫
        stageTransformationCylinder r η hη ▷ Δ[1] ≫ stageCylinder r W := by
  ext n z : 4
  exact stageTransformationFunction_structure r η hη n z.1.1 z.1.2 z.2

lemma stageTransformationTopHomotopy_structure (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {F G : V ⟶ W} (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (s t : unitInterval) (x : stageSpace r V) :
    stageTransformationTopHomotopy (r+1) η hη (s, stageLoopMap r V x t) =
      stageLoopMap r W (stageTransformationTopHomotopy r η hη (s,x)) t :=
  realizationSimplicialHomotopy_interchange (stageTransformationHomotopy r η hη)
    (stageHomotopy r V) (stageTransformationHomotopy (r+1) η hη) (stageHomotopy r W)
    (stageTransformationCylinder_structure r η hη) s t x

end CategoryTheory.Waldhausen.IteratedS
