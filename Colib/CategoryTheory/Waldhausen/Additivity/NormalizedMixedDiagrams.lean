/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedPushout
public import Colib.CategoryTheory.Waldhausen.Additivity.MixedDiagrams
public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalEndpoints

/-! # Chosen-zero normalized mixed-ordinal diagrams

Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedMixedDiagrams.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open SSet.MixedOrdinalCylinder
universe u v u' v'

namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (V : Structure C) (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)
variable {n m : SimplexCategory}

/-- The actual mixed-ordinal deformation, with the nerve degree unchanged. -/
def normalizedMixedGrid (φ : Cut n) (A : Grid₂ (mixedOrdinal φ) m ⥤ C) : Grid₂ n m ⥤ D :=
  normalizedIntervalDiagram V W a hF hG hc (firstIndex φ) (switchedIndex φ)
    (firstIndex_le_switchedIndex φ) A

/-- Every mixed input gives an actual S-diagram in the original outer degree. -/
theorem normalizedMixedGrid_isSimplex₂ (φ : Cut n) {A : Grid₂ (mixedOrdinal φ) m ⥤ C}
    (hA : IsSimplex₂ V.cof V.weq A) :
    IsSimplex₂ W.cof W.weq (normalizedMixedGrid V W a hF hG hc φ A) :=
  normalizedIntervalDiagram_isSimplex₂ V W a hF hG hc _ _ _ hA

/-- Independent nerve restriction commutes strictly with the mixed deformation. -/
theorem normalizedMixedGrid_inner {m' : SimplexCategory} (ν : m' ⟶ m)
    (φ : Cut n) (A : Grid₂ (mixedOrdinal φ) m ⥤ C) :
    gridMap₂ (𝟙 n) ν ⋙ normalizedMixedGrid V W a hF hG hc φ A =
      normalizedMixedGrid V W a hF hG hc φ (gridMap₂ (𝟙 (mixedOrdinal φ)) ν ⋙ A) := rfl

/-- Every outer ordinal map commutes with the actual deformation, including
maps which change whether an endpoint lies in the selected suffix. -/
theorem normalizedMixedGrid_outer {n' : SimplexCategory} (μ : n' ⟶ n)
    (φ : Cut n) (A : Grid₂ (mixedOrdinal φ) m ⥤ C) :
    gridMap₂ μ (𝟙 m) ⋙ normalizedMixedGrid V W a hF hG hc φ A =
      normalizedMixedGrid V W a hF hG hc (μ ≫ φ)
        (gridMap₂ (mixedMap μ (fun _ ↦ le_rfl)) (𝟙 m) ⋙ A) := by
  change (gridMap₂ μ (𝟙 m) ⋙ intervalArrows (firstIndex φ) (switchedIndex φ)
    (firstIndex_le_switchedIndex φ) A) ⋙ normalizedPushoutFunctor V W a hF hG hc =
      intervalArrows (firstIndex (μ ≫ φ)) (switchedIndex (μ ≫ φ))
        (firstIndex_le_switchedIndex (μ ≫ φ))
        (gridMap₂ (mixedMap μ (fun _ ↦ le_rfl)) (𝟙 m) ⋙ A) ⋙ normalizedPushoutFunctor V W a hF hG hc
  rw [intervalArrows_outer, intervalArrows_input]
  exact congrArg (fun T ↦ T ⋙ normalizedPushoutFunctor V W a hF hG hc)
    (intervalArrows_congr (firstIndex_naturality μ (fun _ ↦ le_rfl)).symm
      (switchedIndex_naturality μ φ).symm A)

/-- At the zero cut the actual mixed deformation has the ordinary identity
endpoint, with the exact first-copy ordinal maps. -/
theorem normalizedMixedGrid_zero (A : Grid₂ n m ⥤ C) :
    normalizedMixedGrid V W a hF hG hc (zeroCut n) (gridMap₂ (zeroCollapse n) (𝟙 m) ⋙ A) =
      normalizedIntervalDiagram V W a hF hG hc (𝟙 n) (𝟙 n) (fun _ ↦ le_rfl) A := by
  dsimp only [normalizedMixedGrid, normalizedIntervalDiagram]
  rw [intervalArrows_input]
  exact congrArg (fun T ↦ T ⋙ normalizedPushoutFunctor V W a hF hG hc)
    (intervalArrows_congr (firstIndex_zeroCollapse n)
      (by rw [switchedIndex_zero, firstIndex_zeroCollapse]) A)

/-- At the one cut the two restrictions are precisely the two halves of the
ordinary subdivision. -/
theorem normalizedMixedGrid_one (A : Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m ⥤ C) :
    normalizedMixedGrid V W a hF hG hc (oneCut n)
      (gridMap₂ (inclusion (oneCut n)) (𝟙 m) ⋙ A) =
      normalizedIntervalDiagram V W a hF hG hc (SSet.OrdinalJoin.left n n)
        (SSet.OrdinalJoin.right n n)
        (fun i ↦ by
          change i.val ≤ n.len + 1 + i.val
          omega) A := by
  dsimp only [normalizedMixedGrid, normalizedIntervalDiagram]
  rw [intervalArrows_input]
  exact congrArg (fun T ↦ T ⋙ normalizedPushoutFunctor V W a hF hG hc)
    (intervalArrows_congr (firstIndex_inclusion (oneCut n)) (switchedIndex_one_inclusion n) A)

end CategoryTheory.Waldhausen.Additivity
