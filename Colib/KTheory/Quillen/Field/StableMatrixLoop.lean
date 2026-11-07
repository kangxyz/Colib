/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Field.ElementaryProjectiveKOne
public import Colib.Topology.ClassifyingSpace.CompletionFunctorNaturality

/-!
Implementation provenance: `Quillen/KTheory/Field/StableMatrixLoop.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, tracks,
hypotheses, and signs are retained under native mathematical ownership.

# The original finite matrix class as its actual completion numerator loop

The original telescope projection detects the unchanged finite matrix. Its
prescribed projection-inverse basepoint track cancels through the existing
based homotopy. The resulting ambient completion class is the realization of
the original unit-arrow numerator loop, with the original rank-one-power action.
The final equation retains the original completionPositiveKEquiv. Identifying
that class with a capped Q automorphism cylinder remains a separate obligation.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open Topology HomotopyGroup
open scoped Simplicial
open CategoryTheory CategoryTheory.Limits
open StableGeneralLinear.GrothendieckModel
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.directSumSymmetric
  CategoryTheory.Localization.groupoid

namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The original zero-to-rank telescope arrow projects to the identity stable matrix. -/
lemma projection_rankFromZero (n : ℕ) :
    (projection R).map (rankFromZero R n) = 𝟙 (star R) := by
  apply ULift.ext
  exact map_one (StableGeneralLinear.of R n)

/-- The original rank-n matrix edge projects to its unchanged stable inclusion. -/
lemma projection_rankMatrixLoop (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (projection R).map (rankMatrixLoop R n g) =
      AsSmall.up.map (SingleObj.toEnd (StableGeneralLinear.Group R)
        (StableGeneralLinear.of R n g)) :=
  rfl

/-- The actual completed finite numerator loop projects to the original stable matrix edge. -/
theorem projection_sourceNumeratorLoop (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (groupoidCompletionFunctorMap (projection R)).map (sourceNumeratorLoop R n g) =
      (⊤ : MorphismProperty (StableGeneralLinear.stableCategory R)).Q.map
        (AsSmall.up.map (SingleObj.toEnd (StableGeneralLinear.Group R)
          (StableGeneralLinear.of R n g))) := by
  let Q := (⊤ : MorphismProperty (Telescope R)).Q
  let L := groupoidCompletionFunctorMap (projection R)
  have h {X Y} (a : X ⟶ Y) : L.map (Q.map a) =
      (⊤ : MorphismProperty (StableGeneralLinear.stableCategory R)).Q.map ((projection R).map a) :=
    Functor.congr_hom (groupoidCompletionFunctorMap_fac (projection R)) a
  let Q' := (⊤ : MorphismProperty (StableGeneralLinear.stableCategory R)).Q
  have h0 : L.map (Q.map (rankFromZero R n)) = 𝟙 (Q'.obj (star R)) := by
    exact (h (rankFromZero R n)).trans
      ((congrArg Q'.map (projection_rankFromZero R n)).trans (Q'.map_id _))
  have h1 : L.map (Q.map (rankMatrixLoop R n g)) = Q'.map
      (AsSmall.up.map (SingleObj.toEnd (StableGeneralLinear.Group R)
        (StableGeneralLinear.of R n g))) := h (rankMatrixLoop R n g)
  have hi : L.map (inv (Q.map (rankFromZero R n))) = 𝟙 (Q'.obj (star R)) := by
    exact (L.map_inv _).trans ((Groupoid.inv_eq_inv _).symm.trans
      ((congrArg (fun a : End (Q'.obj (star R)) => Groupoid.inv a) h0).trans
        (by simp)))
  have hh := congrArg₂ (fun a b : End (Q'.obj (star R)) => a ≫ b) h0
    (congrArg₂ (fun a b : End (Q'.obj (star R)) => a ≫ b) h1 hi)
  change L.map (Q.map _ ≫ Q.map _ ≫ inv (Q.map _)) = _
  rw [L.map_comp, L.map_comp]
  exact hh.trans (by simp [Q'])

/-- The original categorical finite numerator loop, realized in the actual telescope
fundamental group. -/
def sourceMatrixPiOne (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    HomotopyGroup.Pi 1 (ClassifyingSpace (Telescope R))
      (classifyingSpacePoint (telescopeBase R)) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    (classifyingGroupoidCompletionMap (Telescope R) (telescopeBase R) (sourceNumeratorLoop R n g))

/-- The original small-category projection retains the realized finite matrix edge. -/
theorem sourceMatrixPiOne_small_projection (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    HomotopyGroup.map (classifyingSpaceMapUniversal (projection R))
        (classifyingSpaceMapUniversal_point (projection R) (telescopeBase R))
        (sourceMatrixPiOne R n g) =
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        ((classifyingFundamentalGroupoidFunctor (StableGeneralLinear.stableCategory R)).mapEnd
          (star R) (AsSmall.up.map (SingleObj.toEnd (StableGeneralLinear.Group R)
            (StableGeneralLinear.of R n g)))) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  erw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply]
  have h := classifyingGroupoidCompletionMap_naturality (projection R) (telescopeBase R)
    (sourceNumeratorLoop R n g)
  rw [show (groupoidCompletionFunctorMap (projection R)).mapEnd _ (sourceNumeratorLoop R n g) =
    (⊤ : MorphismProperty (StableGeneralLinear.stableCategory R)).Q.map
      (AsSmall.up.map (SingleObj.toEnd (StableGeneralLinear.Group R)
        (StableGeneralLinear.of R n g))) from projection_sourceNumeratorLoop R n g] at h
  have he := Functor.congr_hom
    (toClassifyingGroupoidCompletionFunctor (StableGeneralLinear.stableCategory R))
    (AsSmall.up.map (SingleObj.toEnd (StableGeneralLinear.Group R)
      (StableGeneralLinear.of R n g)))
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
  exact (h.trans he).trans (HomotopyGroup.pi1MulEquivFundamentalGroup.apply_symm_apply _).symm

/-- The original projection and universe homeomorphism retain the standard stable matrix class. -/
theorem sourceMatrixPiOne_projection (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    HomotopyGroup.map (originalTelescopeProjection R) (originalTelescopeProjection_point R)
      (sourceMatrixPiOne R n g) =
      GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)
        (StableGeneralLinear.of R n g) := by
  let H := CategoryTheory.asSmallClassifyingHomeomorph
    (SingleObj (StableGeneralLinear.Group R))
  have hp := CategoryTheory.asSmallClassifyingHomeomorph_point
    (SingleObj (StableGeneralLinear.Group R)) (SingleObj.star _)
  have hc : H.toHomotopyEquiv.toFun.comp (originalTelescopeProjection R) =
      classifyingSpaceMapUniversal (projection R) := by
    calc
      _ = (classifyingSpaceMap (projection R)).hom := by
        ext x
        exact H.apply_symm_apply _
      _ = _ := (classifyingSpaceMapUniversal_eq (projection R)).symm
  have hbg : HomotopyGroup.map H.toHomotopyEquiv.toFun hp
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)
        (StableGeneralLinear.of R n g)) =
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      ((classifyingFundamentalGroupoidFunctor (StableGeneralLinear.stableCategory R)).mapEnd
        (star R) (AsSmall.up.map (SingleObj.toEnd (StableGeneralLinear.Group R)
          (StableGeneralLinear.of R n g)))) := by
    apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
    have he := HomotopyGroup.pi1MulEquivFundamentalGroup_naturality H.toHomotopyEquiv.toFun hp
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)
        (StableGeneralLinear.of R n g))
    have hs : HomotopyGroup.pi1MulEquivFundamentalGroup
        (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)
          (StableGeneralLinear.of R n g)) =
      (classifyingFundamentalGroupoidFunctor (SingleObj (StableGeneralLinear.Group R))).mapEnd
        (SingleObj.star _) (SingleObj.toEnd (StableGeneralLinear.Group R)
          (StableGeneralLinear.of R n g)) := by
      erw [GroupoidClassifying.singleObjPiOneEquiv_apply, MulEquiv.apply_symm_apply]
    have ht := congrArg (FundamentalGroup.mapOfEq H.toHomotopyEquiv.toFun hp) hs
    have hf : FundamentalGroup.mapOfEq H.toHomotopyEquiv.toFun hp
        ((classifyingFundamentalGroupoidFunctor (SingleObj (StableGeneralLinear.Group R))).mapEnd
          (SingleObj.star _) (SingleObj.toEnd (StableGeneralLinear.Group R)
            (StableGeneralLinear.of R n g))) =
        (classifyingFundamentalGroupoidFunctor (StableGeneralLinear.stableCategory R)).mapEnd
          (star R) (AsSmall.up.map (SingleObj.toEnd (StableGeneralLinear.Group R)
            (StableGeneralLinear.of R n g))) := by
      rw [FundamentalGroup.mapOfEq_apply]
      change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      let a := SingleObj.toEnd (StableGeneralLinear.Group R) (StableGeneralLinear.of R n g)
      change SSet.toTop.map (asSmallNerveIso (SingleObj (StableGeneralLinear.Group R))).hom
        (SSet.realizationEdgePath (CategoryTheory.nerve.edgeMk a) t) = _
      have ha : (asSmallNerveIso (SingleObj (StableGeneralLinear.Group R))).hom.app
          (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ a) =
          ComposableArrows.mk₁ (AsSmall.up.map a) :=
        ComposableArrows.ext₁ rfl rfl (by simp [asSmallNerveIso])
      exact (SSet.realizationEdgePath_naturality_apply
        (asSmallNerveIso (SingleObj (StableGeneralLinear.Group R))).hom
        (CategoryTheory.nerve.edgeMk a) t).trans
          (congrArg (fun e : (nerve (StableGeneralLinear.stableCategory R)) _⦋1⦌ =>
            SSet.toTop.map (SSet.yonedaEquiv.symm e) (SSet.realizationInterval t)) ha)
    exact he.trans (ht.trans (hf.trans
      (HomotopyGroup.pi1MulEquivFundamentalGroup.apply_symm_apply _).symm))
  apply (homotopyGroupMap_bijective_of_homotopyEquiv H.toHomotopyEquiv hp 1).injective
  exact (HomotopyGroup.map_comp (originalTelescopeProjection R)
    (originalTelescopeProjection_point R) H.toHomotopyEquiv.toFun hp
    (sourceMatrixPiOne R n g)).symm.trans
    ((congrFun (homotopyGroupMap_congr hc _ _) (sourceMatrixPiOne R n g)).trans
      ((sourceMatrixPiOne_small_projection R n g).trans hbg.symm))

/-- The original inverse correction identifies the native stable class with the telescope
numerator. -/
theorem stableGroupPiOneMap_matrix_telescope (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    stableGroupPiOneMap R (StableGeneralLinear.of R n g) =
      HomotopyGroup.map (telescopeZeroMap R) (telescopeZeroMap_point R)
        (sourceMatrixPiOne R n g) := by
  change pathTransport (basepointPath R) 1 (HomotopyGroup.map (stableZeroMap R) rfl
    (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)
      (StableGeneralLinear.of R n g))) = _
  rw [← sourceMatrixPiOne_projection]
  exact stableZeroMap_homotopyGroupMap_projection R 1 (sourceMatrixPiOne R n g)


/-- Component inclusion gives exactly the original completed numerator loop’s realized class. -/
theorem stableGroupPiOneMap_matrix_inclusion (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    HomotopyGroup.map (pathComponentInclusion (zeroPoint R)) (x := zeroBase R) rfl
      (stableGroupPiOneMap R (StableGeneralLinear.of R n g)) =
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (classifyingGroupoidCompletionMap (Completion R) (stageObject R 0)
        (GroupCompletion.Localization.numeratorLoop (StableFree.powerEndEquiv R n g))) := by
  rw [stableGroupPiOneMap_matrix_telescope]
  rw [← HomotopyGroup.map_comp (telescopeZeroMap R) (telescopeZeroMap_point R)
    (pathComponentInclusion (zeroPoint R)) rfl]
  change HomotopyGroup.map (telescopeMap R)
    (classifyingSpaceMapUniversal_point (telescopeFunctor R) (telescopeBase R))
      (sourceMatrixPiOne R n g) = _
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  have he := HomotopyGroup.pi1MulEquivFundamentalGroup_naturality (telescopeMap R)
    (classifyingSpaceMapUniversal_point (telescopeFunctor R) (telescopeBase R))
    (sourceMatrixPiOne R n g)
  have hs : HomotopyGroup.pi1MulEquivFundamentalGroup (sourceMatrixPiOne R n g) =
      classifyingGroupoidCompletionMap (Telescope R) (telescopeBase R)
        (sourceNumeratorLoop R n g) :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.apply_symm_apply _
  have ht := congrArg (FundamentalGroup.mapOfEq (telescopeMap R)
    (classifyingSpaceMapUniversal_point (telescopeFunctor R) (telescopeBase R))) hs
  have hn := classifyingGroupoidCompletionMap_naturality (telescopeFunctor R)
    (telescopeBase R) (sourceNumeratorLoop R n g)
  have hm := congrArg (classifyingGroupoidCompletionMap (Completion R) (stageObject R 0))
    (map_sourceNumeratorLoop R n g)
  exact he.trans (ht.trans (hn.trans (hm.trans
    (HomotopyGroup.pi1MulEquivFundamentalGroup.apply_symm_apply _).symm)))

/-- The canonical quotient-Q matrix value is the original completion comparison of that
numerator. -/
theorem elementaryProjectiveKOneEquiv_matrix_numerator (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    elementaryProjectiveKOneEquiv R
      (StableGeneralLinear.quotientMap R (StableGeneralLinear.of R n g)) =
    completionPositiveKEquiv Rᵐᵒᵖ (stageObject R 0) 0
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (classifyingGroupoidCompletionMap (Completion R) (stageObject R 0)
          (GroupCompletion.Localization.numeratorLoop (StableFree.powerEndEquiv R n g)))) := by
  rw [elementaryProjectiveKOneEquiv_quotientMap, zeroCompletionPositiveKEquiv_apply]
  exact congrArg (completionPositiveKEquiv Rᵐᵒᵖ (stageObject R 0) 0)
    (stableGroupPiOneMap_matrix_inclusion R n g)

end ModuleCat.FiniteProjective.StableCompletion
