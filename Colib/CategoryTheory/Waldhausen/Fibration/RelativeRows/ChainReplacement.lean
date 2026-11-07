/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.FiltrationEquivalence
public import Colib.CategoryTheory.Waldhausen.Fibration.MixedChainReplacement

/-! # Actual relative-row replacement of an original coarse-weak chain

The existing finite cylinder replacement produces a genuine cofibration chain.
The genuine zero-augmented cofiber completion turns it into an actual relative
row. The natural projection is the original cylinder projection preceded by
the inverse of the actual quotient-by-zero isomorphism. It is coarse-weak;
no fine comparison or homotopy equivalence is asserted for that projection.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/ChainReplacement.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.FunctorialFactorization


noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
open FunctorialFactorization
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The coarse-weak arrow predicate on the unchanged original finite chains. -/
def coarseWeakChains (n : SimplexCategory) : ObjectProperty (ComposableArrows C n.len) :=
  fun F ↦ ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), N.coarse.weq (F.map f)

/-- No cofibration predicate is imposed on these original chain arrows. -/
abbrev CoarseWeakChain (n : SimplexCategory) := (coarseWeakChains N n).FullSubcategory

variable (D : FunctorialFactorization N.coarse) [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- The original finite replacement, restricted by its genuinely proved arrow properties. -/
def replacementChainFunctor (n : SimplexCategory) :
    CoarseWeakChain N n ⥤ CofibrationWeakChain N n :=
  (cofibrationWeakChains N n).lift ((coarseWeakChains N n).ι ⋙ finiteReplacement D n.len)
    (fun F ↦ ⟨fun f ↦ MixedChainReplacement.finiteReplacement_map_fine_cof N D n.len F.obj f,
      fun f ↦ MixedChainReplacement.finiteReplacement_map_coarse N D n.len F.obj f (F.property f)⟩)

/-- Genuine relative-row replacement by the existing cylinder and actual cofiber completion. -/
def relativeReplacement (n : SimplexCategory) : CoarseWeakChain N n ⥤ Obj N n :=
  replacementChainFunctor N D n ⋙ completionFunctor N n

/-- The actual completed replacement has the existing finite replacement as its initial chain. -/
def replacementInitialIso (n : SimplexCategory) :
    replacementChainFunctor N D n ⋙ (cofibrationWeakChains N n).ι ≅
      relativeReplacement N D n ⋙ initialFiltrationFunctor N n :=
  NatIso.ofComponents (fun F ↦ relativeCompletionInitialIso N
    ((replacementChainFunctor N D n).obj F).obj
    ((replacementChainFunctor N D n).obj F).property.1
    ((replacementChainFunctor N D n).obj F).property.2) (by
      intro F G f
      exact relativeCompletionUnit_naturality N
        ((replacementChainFunctor N D n).obj F).property.1
        ((replacementChainFunctor N D n).obj F).property.2
        ((replacementChainFunctor N D n).obj G).property.1
        ((replacementChainFunctor N D n).obj G).property.2
        ((finiteReplacement D n.len).map f.hom))

/-- The original cylinder projection, transported through the actual quotient-by-zero
isomorphism. -/
def relativeReplacementProjection (n : SimplexCategory) :
    relativeReplacement N D n ⋙ initialFiltrationFunctor N n ⟶ (coarseWeakChains N n).ι :=
  (replacementInitialIso N D n).inv ≫
    Functor.whiskerLeft (coarseWeakChains N n).ι (finiteProjection D n.len)

/-- Every projection component is literally the original two displayed factors. -/
@[simp] theorem relativeReplacementProjection_app (n : SimplexCategory)
    (F : CoarseWeakChain N n) (i : Fin (n.len + 1)) :
    ((relativeReplacementProjection N D n).app F).app i =
      ((replacementInitialIso N D n).inv.app F).app i ≫
        ((finiteProjection D n.len).app F.obj).app i := rfl

/-- The displayed natural projection is genuinely coarse-weak at each original vertex. -/
theorem relativeReplacementProjection_coarse (n : SimplexCategory)
    (F : CoarseWeakChain N n) (i : Fin (n.len + 1)) :
    N.coarse.weq (((relativeReplacementProjection N D n).app F).app i) :=
  N.coarse.weq.comp_mem _ _ (N.coarse.weq_iso _ inferInstance)
    (MixedChainReplacement.finiteProjection_coarse N D n.len F.obj i)

/-- Actual pointwise fine maps remain fine on the replaced cofibration chain. -/
theorem replacementChainFunctor_fine (hD : MixedChainReplacement.PreservesFineSquares N D)
    {n : SimplexCategory} {F G : CoarseWeakChain N n} (f : F ⟶ G)
    (hf : ∀ i, V.weq (f.hom.app i)) :
    chainFineWeak N n ((replacementChainFunctor N D n).map f) :=
  MixedChainReplacement.finiteReplacement_map_fine N D hD n.len f.hom hf

/-- Actual cofiber gluing then preserves fine weakness on the entire completed relative row. -/
theorem relativeReplacement_fine (hD : MixedChainReplacement.PreservesFineSquares N D)
    {n : SimplexCategory} {F G : CoarseWeakChain N n} (f : F ⟶ G)
    (hf : ∀ i, V.weq (f.hom.app i)) :
    (waldhausenStructure N n).weq ((relativeReplacement N D n).map f) :=
  completionFunctor_weak N ((replacementChainFunctor N D n).map f)
    (replacementChainFunctor_fine N D hD f hf)

/-- At the original first vertex the cylinder replacement itself is unchanged. -/
@[simp] theorem replacementChainFunctor_obj_zero (n : SimplexCategory) (F : CoarseWeakChain N n) :
    ((replacementChainFunctor N D n).obj F).obj.obj 0 = F.obj.obj 0 :=
  MixedChainReplacement.finiteReplacement_initial N D n.len F.obj

end CategoryTheory.Waldhausen.Fibration.RelativeRows
