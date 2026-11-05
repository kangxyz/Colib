/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.NaturalTransformation.HExt
public import Colib.CategoryTheory.Waldhausen.Additivity.DeformationMap
public import Colib.CategoryTheory.Waldhausen.Additivity.SumDiagrams

/-! # Coherence of the actual endpoint natural isomorphisms

Implementation provenance: `Quillen/Waldhausen/Additivity/EndpointNaturality.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
universe u v

namespace CategoryTheory.Waldhausen.Additivity

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F G H : C ⥤ D} (a : F ⟶ G)
variable (hc : IsCofibrationTransformation W a V)

/-- The identity endpoint isomorphism commutes with both ordinal restrictions,
including its actual component maps. -/
theorem identityDeformationIso_reindex {n n' m m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m) (A : Grid₂ n m ⥤ C) :
    HEq (Functor.whiskerLeft (gridMap₂ α β) (identityDeformationIso V W a hc (𝟙 n) A).hom)
      (identityDeformationIso V W a hc (𝟙 n') (gridMap₂ α β ⋙ A)).hom := by
  apply heq_of_eq
  ext x
  simp only [identityDeformationIso, Iso.symm_hom, asIso_inv, Functor.whiskerLeft_app,
    NatIso.isIso_inv_app]
  rfl

/-- The separated arrow construction commutes with simultaneous outer and
inner restriction, with the exact ordinary-subdivision maps. -/
theorem separatedIntervalArrows_reindex {n n' m m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m) (A : Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m ⥤ C) :
    gridMap₂ α β ⋙ intervalArrows (SSet.OrdinalJoin.left n n) (SSet.OrdinalJoin.right n n)
      (left_le_right n) A =
      intervalArrows (SSet.OrdinalJoin.left n' n') (SSet.OrdinalJoin.right n' n') (left_le_right n')
        (gridMap₂ (SSet.OrdinalSubdivision.δ.map α) β ⋙ A) := by
  change intervalArrows (α ≫ SSet.OrdinalJoin.left n n) (α ≫ SSet.OrdinalJoin.right n n)
      (fun i ↦ left_le_right n (α.toOrderHom i))
      (gridMap₂ (𝟙 (SSet.OrdinalSubdivision.δ.obj n)) β ⋙ A) =
    intervalArrows (SSet.OrdinalJoin.left n' n') (SSet.OrdinalJoin.right n' n') (left_le_right n')
      (gridMap₂ (SSet.OrdinalSubdivision.δ.map α) (𝟙 m') ⋙
        gridMap₂ (𝟙 (SSet.OrdinalSubdivision.δ.obj n)) β ⋙ A)
  rw [intervalArrows_input]
  exact intervalArrows_congr (SSet.OrdinalSubdivision.first.naturality α)
    (SSet.OrdinalSubdivision.second.naturality α) _

variable [HasBinaryCoproducts D]
variable (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- Canonical cofiber endpoint maps are unchanged by equality of the actual
input arrow; all displayed cofiber and zero witnesses are propositions. -/
theorem cofiberEndpointIso_hom_heq {f g : Arrow C} (hfg : f = g)
    (hf : F.map f.hom = zeroMorphism W (F.obj f.left) (F.obj f.right))
    (hg : F.map g.hom = zeroMorphism W (F.obj g.left) (F.obj g.right)) :
    HEq (cofiberEndpointIso W a hs.cofibration.app_cof f (b.app f.left) (hs.cofiber f.left) hf).hom
      (cofiberEndpointIso W a hs.cofibration.app_cof g (b.app g.left) (hs.cofiber g.left)
        hg).hom := by
  subst g
  rfl

/-- The actual separated endpoint isomorphism is coherent componentwise
under independent reindexing in both degrees. -/
theorem separatedDeformationIso_reindex_app {n n' m m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m) {A : Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m ⥤ C}
    (hA : IsSimplex₂ V.cof V.weq A) (x : Grid₂ n' m') :
    HEq ((separatedDeformationIso V W a (SSet.OrdinalJoin.left n n) (SSet.OrdinalJoin.right n n)
        (left_le_right n) (left_separated_right n) b hs hA).hom.app ((gridMap₂ α β).obj x))
      ((separatedDeformationIso V W a (SSet.OrdinalJoin.left n' n') (SSet.OrdinalJoin.right n' n')
        (left_le_right n') (left_separated_right n') b hs
          (hA.precomp V.cof V.weq (SSet.OrdinalSubdivision.δ.map α) β)).hom.app x) := by
  refine cofiberEndpointIso_hom_heq V W a b hs
    (congrArg (fun T ↦ T.obj x) (separatedIntervalArrows_reindex α β A)) ?_ ?_
  · exact (congrArg F.map (intervalArrows_separated_hom V (SSet.OrdinalJoin.left n n)
    (SSet.OrdinalJoin.right n
    n) (left_le_right n)
      (left_separated_right n) hA ((gridMap₂ α β).obj x))).trans
      (map_zeroMorphism V W hs.exactF _ _)
  · exact (congrArg F.map (intervalArrows_separated_hom V (SSet.OrdinalJoin.left n' n')
    (SSet.OrdinalJoin.right
    n' n') (left_le_right n')
      (left_separated_right n') (hA.precomp V.cof V.weq (SSet.OrdinalSubdivision.δ.map α)
        β) x)).trans
      (map_zeroMorphism V W hs.exactF _ _)

end CategoryTheory.Waldhausen.Additivity
