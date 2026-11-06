/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.RealizationRows
public import Colib.CategoryTheory.TheoremB.Comparison

/-!
# The transition maps in realized simplicial-replacement rows

The disjoint-union presentation of each row intertwines every simplex
operator with the genuine realized transition map at its first vertex.
This is the local input for the remaining homotopy-cartesian realization
theorem; no passage from rows to total fibers is asserted here.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/Rows.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual comma categories, nerves and
path-space maps are retained; no fiber-equivalence conclusion is assumed. -/
@[expose] public section


noncomputable section

open Topology CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremB

/-- A map of disjoint simplicial unions may change the summand index. -/
def sigmaReindexMap {ι κ : Type u} {X : ι → SSet.{u}} {Y : κ → SSet.{u}}
    (a : ι → κ) (f : ∀ i, X i ⟶ Y (a i)) :
    SSet.simplicialSigma X ⟶ SSet.simplicialSigma Y where
  app n := ↾fun x ↦ ⟨a x.1, (f x.1).app n x.2⟩
  naturality n m α := by
    ext ⟨i, x⟩ : 3
    exact congrArg (Sigma.mk (a i)) (ConcreteCategory.congr_hom ((f i).naturality α) x)

@[reassoc (attr := simp)]
theorem sigmaReindexMap_inclusion {ι κ : Type u} {X : ι → SSet.{u}} {Y : κ → SSet.{u}}
    (a : ι → κ) (f : ∀ i, X i ⟶ Y (a i)) (i : ι) :
    SSet.simplicialSigmaι X i ≫ sigmaReindexMap a f =
      f i ≫ SSet.simplicialSigmaι Y (a i) := rfl

/-- The corresponding continuous map of topological disjoint unions. -/
def sigmaReindexContinuousMap {ι κ : Type u} {X : ι → Type u} {Y : κ → Type u}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (a : ι → κ) (f : ∀ i, C(X i, Y (a i))) : C((Σ i, X i), Σ j, Y j) :=
  ContinuousMap.sigma fun i ↦ (ContinuousMap.sigmaMk (a i)).comp (f i)

/-- Realization of reindexed disjoint unions is exactly the reindexed map of
realizations, including its prescribed action on every summand. -/
theorem realizationSigmaIso_reindex {ι κ : Type u}
    {X : ι → SSet.{u}} {Y : κ → SSet.{u}}
    (a : ι → κ) (f : ∀ i, X i ⟶ Y (a i)) :
    SSet.toTop.map (sigmaReindexMap a f) ≫ (SSet.realizationSigmaIso Y).hom =
      (SSet.realizationSigmaIso X).hom ≫
        TopCat.ofHom (sigmaReindexContinuousMap a fun i ↦ (SSet.toTop.map (f i)).hom) := by
  apply (SSet.realizedSigmaIsColimit X).hom_ext
  intro ⟨i⟩
  dsimp
  rw [← Category.assoc, ← Functor.map_comp, sigmaReindexMap_inclusion, Functor.map_comp,
    Category.assoc, SSet.realizationSigmaIso_ι, ← Category.assoc,
    SSet.realizationSigmaIso_ι]
  rfl

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- A simplex operator acts on the actual topological replacement row by its
base-chain map and the diagram transition at the first vertex. -/
def topologicalRowMap {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    C((Σ s : (nerve D).obj p, |H.obj (s.obj 0)|),
      Σ s : (nerve D).obj q, |H.obj (s.obj 0)|) :=
  sigmaReindexContinuousMap ((nerve D).map α)
    (fun s ↦ (SSet.toTop.map (H.map (TheoremA.firstVertexEdge α s))).hom)

/-- The row realization homeomorphisms respect every simplex operator. -/
theorem replacementRowRealizationIso_naturality {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    SSet.toTop.map (TheoremA.replacementRowMap H α) ≫
      (TheoremA.replacementRowRealizationIso H q).hom =
      (TheoremA.replacementRowRealizationIso H p).hom ≫ TopCat.ofHom (topologicalRowMap H α) :=
  realizationSigmaIso_reindex
    (X := fun s : (nerve D).obj p ↦ H.obj (s.obj 0))
    (Y := fun s : (nerve D).obj q ↦ H.obj (s.obj 0))
    ((nerve D).map α) (fun s ↦ H.map (TheoremA.firstVertexEdge α s))

/-- The topological simplicial replacement, with each level displayed as
an actual disjoint union of the realized fibers. -/
def topologicalReplacement : SimplexCategoryᵒᵖ ⥤ TopCat.{u} where
  obj p := TopCat.of (Σ s : (nerve D).obj p, |H.obj (s.obj 0)|)
  map α := TopCat.ofHom (topologicalRowMap H α)
  map_id p := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change (Sigma.mk ((nerve D).map (𝟙 p) s)
      (SSet.toTop.map (H.map (TheoremA.firstVertexEdge (𝟙 p) s)) x) :
      Σ s : (nerve D).obj p, |H.obj (s.obj 0)|) = ⟨s, x⟩
    simp
    rfl
  map_comp {p q r} α β := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change (Sigma.mk ((nerve D).map (α ≫ β) s)
      (SSet.toTop.map (H.map (TheoremA.firstVertexEdge (α ≫ β) s)) x) :
      Σ s : (nerve D).obj r, |H.obj (s.obj 0)|) =
      Sigma.mk ((nerve D).map β ((nerve D).map α s))
        (SSet.toTop.map (H.map (TheoremA.firstVertexEdge β ((nerve D).map α s)))
          (SSet.toTop.map (H.map (TheoremA.firstVertexEdge α s)) x))
    simp only [Functor.map_comp, TheoremA.firstVertexEdge_comp, TopCat.comp_app]
    rfl

/-- The disjoint-union presentations are an isomorphism of simplicial
spaces, not only a collection of unrelated levelwise homeomorphisms. -/
def topologicalReplacementIso :
    TheoremA.simplicialReplacement H ⋙ SSet.toTop ≅ topologicalReplacement H :=
  NatIso.ofComponents (TheoremA.replacementRowRealizationIso H)
    (fun α ↦ replacementRowRealizationIso_naturality H α)

/-- The actual simplicial-space map to the discrete spaces of base chains. -/
def topologicalReplacementProjection :
    topologicalReplacement H ⟶ nerve D ⋙ TopCat.discrete where
  app p := TopCat.ofHom (Y := TopCat.discrete.obj ((nerve D).obj p))
    ⟨Sigma.fst, continuous_sigma fun _ ↦ continuous_const⟩
  naturality p q α := by
    ext ⟨s, x⟩
    rfl

/-- In the comma diagram, the row's component map is exactly the transition
map appearing in Quillen's Theorem B hypothesis. -/
@[simp]
theorem commaRowTransition {C : Type u} [SmallCategory C] (F : C ⥤ D)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (s : (nerve D).obj p)
    (x : ClassifyingSpace (CostructuredArrow F (s.obj 0))) :
    topologicalRowMap (TheoremA.commaNerveDiagram F) α ⟨s, x⟩ =
      ⟨(nerve D).map α s, transitionMap F (TheoremA.firstVertexEdge α s) x⟩ := rfl

/-- Theorem B's hypothesis supplies a genuine homotopy equivalence for every
component of every simplicial operator on the realized comma replacement. -/
def commaRowTransitionHomotopyEquiv {C : Type u} [SmallCategory C] (F : C ⥤ D)
    (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (s : (nerve D).obj p) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow F (s.obj 0)))
      (ClassifyingSpace (CostructuredArrow F (((nerve D).map α s).obj 0))) :=
  transitionHomotopyEquiv F h (TheoremA.firstVertexEdge α s)

@[simp]
theorem commaRowTransitionHomotopyEquiv_apply {C : Type u} [SmallCategory C]
    (F : C ⥤ D) (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (s : (nerve D).obj p)
    (x : ClassifyingSpace (CostructuredArrow F (s.obj 0))) :
    commaRowTransitionHomotopyEquiv F h α s x =
      transitionMap F (TheoremA.firstVertexEdge α s) x := rfl

end CategoryTheory.TheoremB
