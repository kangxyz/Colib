/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.MixedDiagrams
public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalBisimplicial

/-! # The actual bisimplicial map of the additivity deformation

Implementation provenance: `Quillen/Waldhausen/Additivity/DeformationMap.lean`
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

set_option maxHeartbeats 800000 in
-- Naturality normalizes dependent mixed-ordinal grid and pushout functors beyond the default
-- budget.
/-- The actual mixed-cylinder deformation is a bisimplicial map. Its values
are the genuine pushouts, not chosen equivalences or unspecified fillers. -/
def mixedDeformationMap : outerCylinder (bisimplicialSSet V) ⟶ bisimplicialSSet W where
  app n := {
    app m := ↾fun s ↦ ⟨mixedDeformedGrid V W a hc s.1 s.2.1,
      mixedDeformedGrid_isSimplex₂ V W a hF hG hc s.1 s.2.2⟩
    naturality m m' ν := by
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      exact (mixedDeformedGrid_inner V W a hc ν.unop s.1 s.2.1).symm }
  naturality n n' μ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact (mixedDeformedGrid_outer V W a hc μ.unop s.1 s.2.1).symm

/-- The auxiliary identity endpoint uses actual identity-interval arrows. -/
def identityDeformationMap : bisimplicialSSet V ⟶ bisimplicialSSet W where
  app n := {
    app m := ↾fun A ↦ ⟨deformedGrid V W a hc (𝟙 n.unop) (𝟙 n.unop) (fun _ ↦ le_rfl) A.1,
      deformedGrid_isSimplex₂ V W a hF hG hc _ _ _ A.2⟩
    naturality _ _ _ := by ext A; rfl }
  naturality _ _ _ := by ext m A; rfl

/-- The zero-cut restriction agrees exactly with the actual identity deformation. -/
theorem mixedDeformationMap_zero :
    outerZeroSection (bisimplicialSSet V) ≫ mixedDeformationMap V W a hF hG hc =
      identityDeformationMap V W a hF hG hc := by
  ext n m A
  apply Subtype.ext
  exact mixedDeformedGrid_zero V W a hc A.1

/-- Pointwise order between the two genuine halves of the ordinary subdivision. -/
theorem left_le_right (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (SSet.OrdinalJoin.left n n).toOrderHom i ≤ (SSet.OrdinalJoin.right n n).toOrderHom i := by
  change i.val ≤ n.len + 1 + i.val
  omega

/-- Every vertex in the first half precedes every vertex in the second half. -/
theorem left_separated_right (n : SimplexCategory) (i j : Fin (n.len + 1)) :
    (SSet.OrdinalJoin.left n n).toOrderHom j ≤ (SSet.OrdinalJoin.right n n).toOrderHom i := by
  change j.val ≤ n.len + 1 + i.val
  have := j.isLt
  omega

/-- The auxiliary one endpoint uses the two actual halves of ordinary subdivision. -/
def separatedDeformationMap :
    SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V ⟶ bisimplicialSSet W where
  app n := {
    app m := ↾fun A ↦ ⟨deformedGrid V W a hc (SSet.OrdinalJoin.left n.unop n.unop)
        (SSet.OrdinalJoin.right n.unop n.unop) (left_le_right n.unop) A.1,
      deformedGrid_isSimplex₂ V W a hF hG hc _ _ _ A.2⟩
    naturality _ _ _ := by ext A; rfl }
  naturality n n' μ := by
    ext m A
    apply Subtype.ext
    change intervalArrows (SSet.OrdinalJoin.left n'.unop n'.unop) (SSet.OrdinalJoin.right
      n'.unop n'.unop)
        (left_le_right n'.unop) (gridMap₂ (SSet.OrdinalSubdivision.δ.map μ.unop) (𝟙 m.unop) ⋙ A.1) ⋙
        pushoutFunctor W a hc.app_cof =
      (gridMap₂ μ.unop (𝟙 m.unop) ⋙ intervalArrows (SSet.OrdinalJoin.left n.unop n.unop)
        (SSet.OrdinalJoin.right n.unop n.unop) (left_le_right n.unop) A.1) ⋙
          pushoutFunctor W a hc.app_cof
    rw [intervalArrows_input, intervalArrows_outer]
    exact congrArg (fun T ↦ T ⋙ pushoutFunctor W a hc.app_cof)
      (intervalArrows_congr (SSet.OrdinalSubdivision.first.naturality μ.unop).symm
        (SSet.OrdinalSubdivision.second.naturality μ.unop).symm A.1)

/-- The one-cut restriction agrees exactly with the separated-half deformation. -/
theorem mixedDeformationMap_one :
    outerOneSection (bisimplicialSSet V) ≫ mixedDeformationMap V W a hF hG hc =
      separatedDeformationMap V W a hF hG hc := by
  ext n m A
  apply Subtype.ext
  exact mixedDeformedGrid_one V W a hc A.1

end CategoryTheory.Waldhausen.Additivity
