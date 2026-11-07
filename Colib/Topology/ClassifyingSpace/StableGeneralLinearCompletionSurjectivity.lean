/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionBased
public import Colib.CategoryTheory.GroupCompletion.UnitRoofs
public import Colib.Topology.ClassifyingSpace.CompletionMapSurjectivity

/-!
# Original finite matrix representatives for completed projective zero loops

Actual finite zigzags reduce to single projective automorphisms, and an actual
projective complement turns each numerator into a labelled finite matrix.
No invariant basis number or cancellation of ranks is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Topology SSet HomotopyGroup CategoryTheory.Limits MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.directSumSymmetric
  CategoryTheory.Localization.groupoid

namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The original stage-zero translation is the canonical original unit arrow. -/
lemma stageSequence_from_zero (n : ℕ) :
    (stageSequence R).map (homOfLE (Nat.zero_le n)) =
      GroupCompletion.Localization.unitArrow (𝟙 (rankOnePower Rᵐᵒᵖ n)) := by
  induction n with
  | zero =>
    change (stageSequence R).map (𝟙 0) = _
    rw [(stageSequence R).map_id]
    exact GroupCompletion.Localization.unitArrow_unit.symm
  | succ n ih =>
    rw [← homOfLE_comp (Nat.zero_le n) (Nat.le_succ n),
      (stageSequence R).map_comp]
    rw [show (stageSequence R).map (homOfLE (Nat.le_succ n)) = stageArrow R n from
      Functor.ofSequence_map_homOfLE_succ _ n, ih]
    exact (GroupCompletion.Localization.unitArrow_translation
      (𝟙 (rankOnePower Rᵐᵒᵖ n)) (freeIso Rᵐᵒᵖ 1)).trans
        (congrArg GroupCompletion.Localization.unitArrow (MonoidalCategory.whiskerLeft_id _ _))

/-- Every completed zero loop is an original labelled finite-matrix numerator loop. -/
theorem exists_finite_numeratorLoop
    (a : End ((GroupCompletion.Localization.completionFunctor
      (C := IsoCategory Rᵐᵒᵖ)).obj (stageObject R 0))) :
    ∃ n, ∃ g : Matrix.GeneralLinearGroup (Fin n) R,
      a = GroupCompletion.Localization.numeratorLoop (StableFree.powerEndEquiv R n g) := by
  obtain ⟨P, g, ha⟩ := GroupCompletion.Localization.exists_numeratorLoop a
  obtain ⟨n, Q, ⟨e⟩⟩ := rankOne_cofinal Rᵐᵒᵖ P
  let d : Q ⊗ P ≅ rankOnePower Rᵐᵒᵖ n := (β_ Q P) ≪≫ e
  obtain ⟨m, hm⟩ := (StableFree.powerEndEquiv R n).surjective (inv d.hom ≫ Q ◁ g ≫ d.hom)
  refine ⟨n, m, ?_⟩
  rw [hm]
  exact ha.trans ((GroupCompletion.Localization.numeratorLoop_translation g Q).trans
    (GroupCompletion.Localization.numeratorLoop_transport (Q ◁ g) d.hom))

/-- The actual object carrying rank-n matrices in the Grothendieck model. -/
def rankObject (n : ℕ) : StableGeneralLinear.GrothendieckModel.Telescope R :=
  ⟨StableGeneralLinear.rankIndex n, AsSmall.up.obj (SingleObj.star _)⟩

/-- The original identity matrix supplies the arrow from rank zero to rank n. -/
def rankFromZero (n : ℕ) : telescopeBase R ⟶ rankObject R n where
  base := AsSmall.up.map (homOfLE (Nat.zero_le n))
  fiber := ULift.up (1 : Matrix.GeneralLinearGroup (Fin n) R)

/-- A labelled matrix gives the original endomorphism of its Grothendieck fiber. -/
def rankMatrixLoop (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    rankObject R n ⟶ rankObject R n where
  base := 𝟙 _
  fiber := ULift.up g

/-- The original zero-to-rank arrow realizes exactly the original common-denominator translation. -/
lemma telescopeFunctor_rankFromZero (n : ℕ) :
    (telescopeFunctor R).map (rankFromZero R n) =
      GroupCompletion.Localization.unitArrow (𝟙 (rankOnePower Rᵐᵒᵖ n)) := by
  change (stageSequence R).map (homOfLE (Nat.zero_le n)) ≫ stageAction R n 1 = _
  rw [map_one]
  exact (Category.comp_id _).trans (stageSequence_from_zero R n)

/-- The original fiber matrix maps to its original second-coordinate action. -/
lemma telescopeFunctor_rankMatrixLoop (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (telescopeFunctor R).map (rankMatrixLoop R n g) = stageAction R n g := by
  change (stageSequence R).map (𝟙 n) ≫ stageAction R n g = _
  rw [(stageSequence R).map_id, Category.id_comp]

/-- The original localized telescope loop associated to a finite matrix. -/
def sourceNumeratorLoop (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    End ((⊤ : MorphismProperty (StableGeneralLinear.GrothendieckModel.Telescope R)).Q.obj
      (telescopeBase R)) :=
  let Q := (⊤ : MorphismProperty (StableGeneralLinear.GrothendieckModel.Telescope R)).Q
  Q.map (rankFromZero R n) ≫ Q.map (rankMatrixLoop R n g) ≫
    inv (Q.map (rankFromZero R n))

/-- Localization of the original telescope functor preserves the specified finite loop. -/
lemma map_sourceNumeratorLoop (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (groupoidCompletionFunctorMap (telescopeFunctor R)).map (sourceNumeratorLoop R n g) =
      GroupCompletion.Localization.numeratorLoop (StableFree.powerEndEquiv R n g) := by
  let F := telescopeFunctor R
  let Q := (⊤ : MorphismProperty (StableGeneralLinear.GrothendieckModel.Telescope R)).Q
  let L := groupoidCompletionFunctorMap F
  have h {X Y} (f : X ⟶ Y) : L.map (Q.map f) =
      (⊤ : MorphismProperty (Completion R)).Q.map (F.map f) :=
    Functor.congr_hom (groupoidCompletionFunctorMap_fac F) f
  change L.map (Q.map _ ≫ Q.map _ ≫ inv (Q.map _)) = _
  simp only [L.map_comp, L.map_inv, h]
  simp only [F, telescopeFunctor_rankFromZero, telescopeFunctor_rankMatrixLoop]
  rfl

/-- Every completed zero loop lifts along the original categorical telescope functor. -/
theorem telescopeCompletion_mapEnd_surjective :
    Function.Surjective ((groupoidCompletionFunctorMap (telescopeFunctor R)).mapEnd
      ((⊤ : MorphismProperty (StableGeneralLinear.GrothendieckModel.Telescope R)).Q.obj
        (telescopeBase R))) := by
  intro a
  obtain ⟨n, g, ha⟩ := exists_finite_numeratorLoop R a
  exact ⟨sourceNumeratorLoop R n g, (map_sourceNumeratorLoop R n g).trans ha.symm⟩

/-- The actual realized telescope map is surjective on the based fundamental group. -/
theorem telescopeMap_piOne_surjective :
    Function.Surjective (piMap 0 (telescopeMap R)
      (classifyingSpaceMapUniversal_point (telescopeFunctor R) (telescopeBase R))) :=
  classifyingSpaceMapUniversal_piOne_surjective (telescopeFunctor R) (telescopeBase R)
    (telescopeCompletion_mapEnd_surjective R)

end ModuleCat.FiniteProjective.StableCompletion
