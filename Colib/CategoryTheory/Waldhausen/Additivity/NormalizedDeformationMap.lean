/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedMixedDiagrams
public import Colib.CategoryTheory.Waldhausen.Additivity.DeformationMap
public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalBisimplicial

/-! # The chosen-zero normalized deformation maps

Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedDeformationMap.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open SSet.MixedOrdinalCylinder
universe u v

namespace CategoryTheory.Waldhausen.Additivity

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

set_option maxHeartbeats 550000 in
-- Lean 4.34.1 exhausts the default budget elaborating this map's outer naturality.
-- The declaration-local allowance preserves the actual normalized pushout construction.
/-- The actual mixed-cylinder deformation is a bisimplicial map. Its values
are the genuine pushouts, not chosen equivalences or unspecified fillers. -/
def normalizedMixedMap : outerCylinder (bisimplicialSSet V) ⟶ bisimplicialSSet W where
  app n := {
    app m := ↾fun s ↦ ⟨normalizedMixedGrid V W a hF hG hc s.1 s.2.1,
      normalizedMixedGrid_isSimplex₂ V W a hF hG hc s.1 s.2.2⟩
    naturality m m' ν := by
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      exact (normalizedMixedGrid_inner V W a hF hG hc ν.unop s.1 s.2.1).symm }
  naturality n n' μ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact (normalizedMixedGrid_outer V W a hF hG hc μ.unop s.1 s.2.1).symm

/-- The auxiliary identity endpoint uses actual identity-interval arrows. -/
def normalizedIdentityMap : bisimplicialSSet V ⟶ bisimplicialSSet W where
  app n := {
    app m := ↾fun A ↦ ⟨normalizedIntervalDiagram V W a hF hG hc (𝟙 n.unop) (𝟙 n.unop) (fun _ ↦
      le_rfl) A.1,
      normalizedIntervalDiagram_isSimplex₂ V W a hF hG hc _ _ _ A.2⟩
    naturality _ _ _ := by ext A; rfl }
  naturality _ _ _ := by ext m A; rfl

/-- The zero-cut restriction agrees exactly with the actual identity deformation. -/
theorem normalizedMixedMap_zero :
    outerZeroSection (bisimplicialSSet V) ≫ normalizedMixedMap V W a hF hG hc =
      normalizedIdentityMap V W a hF hG hc := by
  ext n m A
  apply Subtype.ext
  exact normalizedMixedGrid_zero V W a hF hG hc A.1

/-- The auxiliary one endpoint uses the two actual halves of ordinary subdivision. -/
def normalizedSeparatedMap :
    SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V ⟶ bisimplicialSSet W where
  app n := {
    app m := ↾fun A ↦ ⟨normalizedIntervalDiagram V W a hF hG hc (SSet.OrdinalJoin.left
      n.unop n.unop)
        (SSet.OrdinalJoin.right n.unop n.unop) (left_le_right n.unop) A.1,
      normalizedIntervalDiagram_isSimplex₂ V W a hF hG hc _ _ _ A.2⟩
    naturality _ _ _ := by ext A; rfl }
  naturality n n' μ := by
    ext m A
    apply Subtype.ext
    change intervalArrows (SSet.OrdinalJoin.left n'.unop n'.unop) (SSet.OrdinalJoin.right
      n'.unop n'.unop)
        (left_le_right n'.unop) (gridMap₂ (SSet.OrdinalSubdivision.δ.map μ.unop) (𝟙 m.unop) ⋙ A.1) ⋙
        normalizedPushoutFunctor V W a hF hG hc =
      (gridMap₂ μ.unop (𝟙 m.unop) ⋙ intervalArrows (SSet.OrdinalJoin.left n.unop n.unop)
        (SSet.OrdinalJoin.right n.unop n.unop) (left_le_right n.unop) A.1) ⋙
          normalizedPushoutFunctor V
          W a hF hG hc
    rw [intervalArrows_input, intervalArrows_outer]
    exact congrArg (fun T ↦ T ⋙ normalizedPushoutFunctor V W a hF hG hc)
      (intervalArrows_congr (SSet.OrdinalSubdivision.first.naturality μ.unop).symm
        (SSet.OrdinalSubdivision.second.naturality μ.unop).symm A.1)

/-- The one-cut restriction agrees exactly with the separated-half deformation. -/
theorem normalizedMixedMap_one :
    outerOneSection (bisimplicialSSet V) ≫ normalizedMixedMap V W a hF hG hc =
      normalizedSeparatedMap V W a hF hG hc := by
  ext n m A
  apply Subtype.ext
  exact normalizedMixedGrid_one V W a hF hG hc A.1

end CategoryTheory.Waldhausen.Additivity
