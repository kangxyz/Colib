/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # Original fine-weak chains with arbitrary natural transformations

At fixed fine-nerve degree the objects are the original finite chains whose
arrows are fine weak equivalences. Morphisms of the underlying full category
are all original natural transformations. Cofibrations and coarse weak maps
are then imposed pointwise, independently of the fine object predicate.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/FineChains.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [Category.{v} C]

/-- Pointwise original arrows on any full subcategory of original finite chains. -/
def pointwise (P : MorphismProperty C) {k : SimplexCategory}
    (S : ObjectProperty (ComposableArrows C k.len)) : MorphismProperty S.FullSubcategory :=
  fun _ _ f ↦ ∀ i, P (f.hom.app i)

instance pointwise_multiplicative (P : MorphismProperty C) [P.IsMultiplicative]
    {k : SimplexCategory} (S : ObjectProperty (ComposableArrows C k.len)) :
    (pointwise P S).IsMultiplicative where
  id_mem _ _ := P.id_mem _
  comp_mem _ _ hf hg i := P.comp_mem _ _ (hf i) (hg i)

instance pointwise_twoOutOfThree (P : MorphismProperty C) [P.HasTwoOutOfThreeProperty]
    {k : SimplexCategory} (S : ObjectProperty (ComposableArrows C k.len)) :
    (pointwise P S).HasTwoOutOfThreeProperty where
  comp_mem _ _ hf hg i := P.comp_mem _ _ (hf i) (hg i)
  of_postcomp f g hg hfg i := P.of_postcomp (f.hom.app i) (g.hom.app i) (hg i) (hfg i)
  of_precomp f g hf hfg i := P.of_precomp (f.hom.app i) (g.hom.app i) (hf i) (hfg i)

variable (V : Structure C)

/-- The actual fine-weak arrow predicate on the unchanged original chain. -/
def fineChains (k : SimplexCategory) : ObjectProperty (ComposableArrows C k.len) :=
  fun F ↦ ∀ {i j : Fin (k.len + 1)} (f : i ⟶ j), V.weq (F.map f)

/-- All natural transformations are retained, before imposing horizontal predicates. -/
abbrev FineChain (k : SimplexCategory) := (fineChains V k).FullSubcategory

/-- Original componentwise cofibrations between fine-weak chains. -/
def pointwiseCof (k : SimplexCategory) : MorphismProperty (FineChain V k) :=
  pointwise V.cof (fineChains V k)

instance pointwiseCof_multiplicative (k : SimplexCategory) : (pointwiseCof V k).IsMultiplicative :=
  pointwise_multiplicative _ _

variable {V} (N : NestedWeakEquivalences V)

/-- Original componentwise coarse weak equivalences between fine-weak chains. -/
def pointwiseCoarse (k : SimplexCategory) : MorphismProperty (FineChain V k) :=
  pointwise N.coarse.weq (fineChains V k)

instance pointwiseCoarse_multiplicative (k : SimplexCategory) :
    (pointwiseCoarse N k).IsMultiplicative := pointwise_multiplicative _ _

instance pointwiseCoarse_twoOutOfThree (k : SimplexCategory)
    [N.coarse.weq.HasTwoOutOfThreeProperty] : (pointwiseCoarse N k).HasTwoOutOfThreeProperty :=
  pointwise_twoOutOfThree _ _

@[simp] theorem pointwiseCof_iff {k : SimplexCategory} {F G : FineChain V k} (f : F ⟶ G) :
    pointwiseCof V k f ↔ ∀ i, V.cof (f.hom.app i) := Iff.rfl

@[simp] theorem pointwiseCoarse_iff {k : SimplexCategory} {F G : FineChain V k} (f : F ⟶ G) :
    pointwiseCoarse N k f ↔ ∀ i, N.coarse.weq (f.hom.app i) := Iff.rfl

variable (V)

/-- Every original ordinal restriction preserves the actual fine-weak object condition. -/
def fineReindex {k l : SimplexCategory} (α : k ⟶ l) : FineChain V l ⥤ FineChain V k where
  obj F := ⟨(SimplexCategory.toCat.map α).toFunctor ⋙ F.obj,
    fun f ↦ F.property ((SimplexCategory.toCat.map α).toFunctor.map f)⟩
  map f := (fineChains V k).homMk
    (Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem fineReindex_obj {k l : SimplexCategory} (α : k ⟶ l) (F : FineChain V l) :
    ((fineReindex V α).obj F).obj = (SimplexCategory.toCat.map α).toFunctor ⋙ F.obj := rfl

@[simp] theorem fineReindex_map_app {k l : SimplexCategory} (α : k ⟶ l)
    {F G : FineChain V l} (f : F ⟶ G) (i : Fin (k.len + 1)) :
    ((fineReindex V α).map f).hom.app i = f.hom.app (α.toOrderHom i) := rfl

@[simp] theorem fineReindex_id (k : SimplexCategory) : fineReindex V (𝟙 k) = 𝟭 (FineChain V k) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem fineReindex_comp {k l m : SimplexCategory} (α : k ⟶ l) (β : l ⟶ m) :
    fineReindex V (α ≫ β) = fineReindex V β ⋙ fineReindex V α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The unchanged ordinal restriction preserves original pointwise cofibrations. -/
theorem fineReindex_cof {k l : SimplexCategory} (α : k ⟶ l)
    {F G : FineChain V l} (f : F ⟶ G) (hf : pointwiseCof V l f) :
    pointwiseCof V k ((fineReindex V α).map f) := fun i ↦ hf (α.toOrderHom i)

/-- The unchanged ordinal restriction preserves original pointwise coarse weak maps. -/
theorem fineReindex_coarse {k l : SimplexCategory} (α : k ⟶ l)
    {F G : FineChain V l} (f : F ⟶ G) (hf : pointwiseCoarse N l f) :
    pointwiseCoarse N k ((fineReindex V α).map f) := fun i ↦ hf (α.toOrderHom i)

end CategoryTheory.Waldhausen.Fibration.MixedNerves
