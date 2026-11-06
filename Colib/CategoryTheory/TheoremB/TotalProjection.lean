/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.CartesianProducts
public import Colib.CategoryTheory.TheoremA.IteratedRealization
public import Colib.CategoryTheory.TheoremA.Augmentations
public import Colib.Topology.Realization.ConstantIso

/-!
# The actual total replacement projection

The coend realization of the displayed topological replacement is compared
homeomorphically with the actual diagonal realization. The corresponding
base coend is homeomorphic to the ordinary nerve realization. These
homeomorphisms identify the total projection with the canonical map of
simplicial sets, including its direction and all simplex maps.
-/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremB/TotalProjection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The previously native constant-realization
isomorphism is reused; the actual coends and augmentation maps are retained. -/
@[expose] public section

noncomputable section

open SSet Topology CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremB

/-- Iterated topological realization is a functor, with the already defined
canonical coend map. -/
def topologicalRealizationFunctor : (SimplexCategoryᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u} where
  obj := TheoremA.iteratedRealization
  map := TheoremA.iteratedRealizationMap
  map_id Y := by
    change coend.map (TheoremA.iteratedRealizationBifunctorMap (𝟙 Y)) = _
    have hi : TheoremA.iteratedRealizationBifunctorMap (𝟙 Y) = 𝟙 _ := by
      ext p q
      simp [TheoremA.iteratedRealizationBifunctorMap]
      rfl
    rw [hi, coend.map_id]
    rfl
  map_comp η θ := by
    change coend.map (TheoremA.iteratedRealizationBifunctorMap (η ≫ θ)) = _
    have hc : TheoremA.iteratedRealizationBifunctorMap (η ≫ θ) =
        TheoremA.iteratedRealizationBifunctorMap η ≫
          TheoremA.iteratedRealizationBifunctorMap θ := by
      ext p q
      simp [TheoremA.iteratedRealizationBifunctorMap]
      rfl
    rw [hc]
    exact (coend.map_comp _ _).symm

/-- The actual realized rows of the base bisimplicial set form precisely
the simplicial discrete space of base chains. -/
def baseRowsRealizationIso (D : Type u) [SmallCategory D] :
    TheoremA.baseBisimplicial D ⋙ SSet.toTop ≅ nerve D ⋙ TopCat.discrete :=
  NatIso.ofComponents (fun p ↦ constantRealizationIso ((nerve D).obj p))
    (fun α ↦ constantRealizationIso_naturality ((nerve D).map α))

/-- The coend realization of the discrete nerve is homeomorphic to its
ordinary simplicial realization. -/
def baseTotalRealizationIso (D : Type u) [SmallCategory D] :
    TheoremA.iteratedRealization (nerve D ⋙ TopCat.discrete) ≅ ClassifyingSpace D :=
  (topologicalRealizationFunctor.mapIso (baseRowsRealizationIso D)).symm ≪≫
    (TheoremA.diagonalIteratedRealizationIso (TheoremA.baseBisimplicial D)).symm ≪≫
      SSet.toTop.mapIso (TheoremA.diagonalBaseIso D)

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The topological replacement's coend is homeomorphic to the actual
realization of its simplicial diagonal. -/
def replacementTotalRealizationIso :
    |TheoremA.replacementDiagonal H| ≅ TheoremA.iteratedRealization (topologicalReplacement H) :=
  TheoremA.diagonalIteratedRealizationIso (TheoremA.simplicialReplacement H) ≪≫
    topologicalRealizationFunctor.mapIso (topologicalReplacementIso H)

/-- In every actual row, the realized target augmentation is the displayed
coproduct projection under the two canonical homeomorphisms. -/
theorem targetAugmentation_row_projection (p : SimplexCategoryᵒᵖ) :
    SSet.toTop.map ((TheoremA.targetAugmentation H).app p) ≫
        (constantRealizationIso ((nerve D).obj p)).hom =
      (TheoremA.replacementRowRealizationIso H p).hom ≫
        (topologicalReplacementProjection H).app p := by
  apply (SSet.realizedSigmaIsColimit
    (fun s : (nerve D).obj p ↦ H.obj (s.obj 0))).hom_ext
  intro ⟨s⟩
  dsimp
  have heq : SSet.simplicialSigmaι
      (fun s : (nerve D).obj p ↦ H.obj (s.obj 0)) s ≫
        (TheoremA.targetAugmentation H).app p =
      SSet.stdSimplex.isTerminalObj₀.from (H.obj (s.obj 0)) ≫
        (SSet.simplicialSigmaι (fun _ : (nerve D).obj p ↦ (Δ[0] : SSet.{u})) s ≫
          (SSet.pointSigmaIso ((nerve D).obj p)).hom) := rfl
  rw [← Functor.map_comp_assoc]
  erw [heq]
  rw [Functor.map_comp_assoc]
  erw [Functor.map_comp, Category.assoc, constantRealizationIso_ι_comp]
  change _ = SSet.toTop.map (SSet.simplicialSigmaι _ s) ≫
    (SSet.realizationSigmaIso _).hom ≫ (topologicalReplacementProjection H).app p
  rw [SSet.realizationSigmaIso_ι_assoc]
  rfl

/-- The row projection identification is an equality of simplicial maps. -/
theorem targetAugmentation_realization_projection :
    Functor.whiskerRight (TheoremA.targetAugmentation H) SSet.toTop ≫
        (baseRowsRealizationIso D).hom =
      (topologicalReplacementIso H).hom ≫ topologicalReplacementProjection H := by
  apply NatTrans.ext
  funext p
  exact targetAugmentation_row_projection H p

/-- The topological coend projection is exactly the realized canonical
simplicial projection after the source and target homeomorphisms. -/
theorem replacementTotalRealizationIso_projection :
    (replacementTotalRealizationIso H).hom ≫
        TheoremA.iteratedRealizationMap (topologicalReplacementProjection H) ≫
          (baseTotalRealizationIso D).hom =
      SSet.toTop.map (TheoremA.replacementBaseMap H) := by
  let R := topologicalRealizationFunctor
  have hn := TheoremA.diagonalIteratedRealizationIso_naturality (TheoremA.targetAugmentation H)
  change SSet.toTop.map (SSet.diagonalMap (TheoremA.targetAugmentation H)) ≫
      (TheoremA.diagonalIteratedRealizationIso (TheoremA.baseBisimplicial D)).hom =
    (TheoremA.diagonalIteratedRealizationIso (TheoremA.simplicialReplacement H)).hom ≫
      R.map (Functor.whiskerRight (TheoremA.targetAugmentation H) SSet.toTop) at hn
  change ((TheoremA.diagonalIteratedRealizationIso (TheoremA.simplicialReplacement H)).hom ≫
    R.map (topologicalReplacementIso H).hom) ≫
    R.map (topologicalReplacementProjection H) ≫
      (R.map (baseRowsRealizationIso D).inv ≫
        (TheoremA.diagonalIteratedRealizationIso (TheoremA.baseBisimplicial D)).inv ≫
          SSet.toTop.map (TheoremA.diagonalBaseIso D).hom) = _
  simp only [Category.assoc]
  rw [← R.map_comp_assoc, ← targetAugmentation_realization_projection]
  rw [R.map_comp_assoc]
  rw [← R.map_comp_assoc (baseRowsRealizationIso D).hom (baseRowsRealizationIso D).inv]
  rw [Iso.hom_inv_id, R.map_id, Category.id_comp]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, TheoremA.targetAugmentation_diagonal]

end CategoryTheory.TheoremB
