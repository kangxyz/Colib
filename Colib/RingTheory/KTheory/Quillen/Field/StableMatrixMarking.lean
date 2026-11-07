/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Quillen.Field.StableMatrixLoop
public import Colib.RingTheory.KTheory.Quillen.ProjectiveCompletionLocalizedContraction
public import Colib.RingTheory.KTheory.Quillen.ProjectiveCompletionAutomorphismHomotopy
public import Colib.RingTheory.KTheory.Quillen.ProjectiveCompletionBasepoint
public import Colib.KTheory.Quillen.Automorphism.ReturnNormalization
public import Colib.KTheory.Quillen.LowDegreeScalarAction.BiproductLoopFamilies
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.FamilyCommutation

/-!
Implementation provenance: `Quillen/KTheory/Field/StableMatrixMarking.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, tracks,
hypotheses, and signs are retained under native mathematical ownership.

# The original matrix quotient-Q comparison and its positive core marking

The actual finite-stage source contracts through the original localized
extension arms. Its stored fiber path and unchanged denominator endpoint path
give the original four-arm return family. The genuine cone homotopy, original
correction paths and actual categorical family commutation identify its positive core class.

The original unit-arrow path and completed numerator then give this formula
for the unchanged elementary quotient-Q equivalence. Every ring, rank and
matrix is included. Transport to the literal upper finite-module cube is a
separate consumer; this file makes no substitute choice of matrix or inverse.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open Topology HomotopyGroup
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped Topology unitInterval ZeroObject
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  CategoryTheory.Localization.groupoid
variable (R : Type u) [Ring R]

/-- The actual classifying space of the original finite matrix category. -/
abbrev MatrixStageSpace (n : ℕ) := ClassifyingSpace (StableGeneralLinear.finiteCategory R n)

/-- Restrict the original completion identity-entry map to the actual finite stage. -/
def stageIdentityMap (n : ℕ) :=
  (classifyingSpaceMapUniversal (completionIdentityEntry Rᵐᵒᵖ)).comp
    (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n))

/-- Restrict the original completion-to-Q homotopy-fiber map to the finite stage. -/
def stageOriginalFiberMap (n : ℕ) :=
  (completionToOriginalQHomotopyFiber Rᵐᵒᵖ).comp
    (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n))

/-- The original stored fiber path with only its exact source-coordinate equality inserted. -/
def originalStageFiberPath (n : ℕ) (z : MatrixStageSpace R n) :
    Path ((classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
      (stageIdentityMap R n z)) (exactStructure Rᵐᵒᵖ).kBasepoint :=
  (HomotopyFiber.toPath _ _ (stageOriginalFiberMap R n z)).cast
    (congrArg (classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
      (completionToOriginalQHomotopyFiber_source Rᵐᵒᵖ
        (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n) z))).symm rfl

/-- The full stored path is the reversed original inverse-quotient transformation track. -/
theorem originalStageFiberPath_apply (n : ℕ) (z : MatrixStageSpace R n) (t : unitInterval) :
    originalStageFiberPath R n z t =
      classifyingSpaceUniversalHomotopy (completionIdentityProjectionIsoZero Rᵐᵒᵖ).inv
        (unitInterval.symm t,
          classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n) z) :=
  completionToOriginalQHomotopyFiber_path Rᵐᵒᵖ _ t

/-- The original fixed denominator paired with the actual zero module. -/
def denominatorZeroPair (n : ℕ) : GroupCompletionCategory Rᵐᵒᵖ :=
  completionPair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) ⟨0⟩

/-- The unchanged original quotient path at the fixed-denominator zero extension. -/
def denominatorZeroPath (n : ℕ) :
    Path ((classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
      (classifyingSpacePoint
        ((fixedDenominatorExtension Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n)).obj
          (exactStructure Rᵐᵒᵖ).extensionTotalPoint))) (exactStructure Rᵐᵒᵖ).kBasepoint :=
  completionQVertexPath Rᵐᵒᵖ (denominatorZeroPair R n)

/-- The unique original object of the finite matrix stage. -/
def stageVertex (n : ℕ) : StableGeneralLinear.finiteCategory R n :=
  AsSmall.up.obj (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R))

/-- The actual finite matrix action in the original power-object core. -/
def stageCore (n : ℕ) := AsSmall.down ⋙ StableFree.powerFunctor R n

/-- The identity-extension diagram of the original finite power action. -/
def stageExtension (n : ℕ) := stageCore R n ⋙ (exactStructure Rᵐᵒᵖ).identityExtensionFunctor

/-- The original fixed-denominator extension inclusion for this finite stage. -/
def stageDenominator (n : ℕ) := fixedDenominatorExtension Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n)

/-- The actual identity-to-raise contraction arm in the localized total space. -/
def stageIdentityArm (n : ℕ) :=
  Functor.whiskerRight (Functor.whiskerLeft (stageExtension R n)
    (Subdivision.identityToInitialRaise (exactStructure Rᵐᵒᵖ).inflationZeroIsInitial))
      (stageDenominator R n)

/-- The actual zero-to-raise contraction arm in the same localized total space. -/
def stageZeroArm (n : ℕ) :=
  Functor.whiskerRight (Functor.whiskerLeft (stageExtension R n)
    (Subdivision.constantToInitialRaise (exactStructure Rᵐᵒᵖ).inflationZeroIsInitial))
      (stageDenominator R n)

/-- The zero arm begins at the original fixed-denominator zero extension. -/
theorem stageZeroFunctor_eq_const (n : ℕ) :
    (stageExtension R n ⋙
      (Functor.const (exactStructure Rᵐᵒᵖ).ExtensionTotal).obj
        (exactStructure Rᵐᵒᵖ).extensionTotalPoint) ⋙ stageDenominator R n =
      (Functor.const (StableGeneralLinear.finiteCategory R n)).obj
        ((stageDenominator R n).obj (exactStructure Rᵐᵒᵖ).extensionTotalPoint) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (stageDenominator R n).map_id _

/-- Universal realization of the actual two categorical arms contracts the original stage
source map. -/
def universalStageSourceContraction (n : ℕ) :
    ((HomotopyFiber.projection
      (classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
        (exactStructure Rᵐᵒᵖ).kBasepoint).comp (stageOriginalFiberMap R n)).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint
        ((stageDenominator R n).obj (exactStructure Rᵐᵒᵖ).extensionTotalPoint))) := by
  let H := (classifyingSpaceUniversalHomotopy (stageIdentityArm R n)).trans
    (classifyingSpaceUniversalHomotopy (stageZeroArm R n)).symm
  refine H.cast ?_ ?_
  · ext z
    change classifyingSpaceMapUniversal (stageExtension R n ⋙ stageDenominator R n) z =
      (stageOriginalFiberMap R n z).val.1
    rw [show (stageOriginalFiberMap R n z).val.1 = stageIdentityMap R n z from
      completionToOriginalQHomotopyFiber_source Rᵐᵒᵖ
        (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n) z)]
    change _ = ((classifyingSpaceMapUniversal (completionIdentityEntry Rᵐᵒᵖ)).comp
      (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n))) z
    rw [← classifyingSpaceMapUniversal_comp, stageIdentity_fixedDenominator]
    rfl
  · change classifyingSpaceMapUniversal
      ((stageExtension R n ⋙
        (Functor.const (exactStructure Rᵐᵒᵖ).ExtensionTotal).obj
          (exactStructure Rᵐᵒᵖ).extensionTotalPoint) ⋙ stageDenominator R n) = _
    rw [stageZeroFunctor_eq_const, classifyingSpaceMapUniversal_const]

/-- Project the original localized identity arm to the actual Q-category. -/
def stageIdentityQArm (n : ℕ) :=
  Functor.whiskerRight (stageIdentityArm R n) (localizedExtensionProjection Rᵐᵒᵖ)

/-- Project the original localized zero arm to the actual Q-category. -/
def stageZeroQArm (n : ℕ) :=
  Functor.whiskerRight (stageZeroArm R n) (localizedExtensionProjection Rᵐᵒᵖ)

/-- Projection retains the complete universal two-arm contraction family. -/
theorem projectedUniversalStageContraction (n : ℕ) (t : unitInterval)
    (z : MatrixStageSpace R n) :
    classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ)
      (universalStageSourceContraction R n (t,z)) =
      ((classifyingSpaceUniversalHomotopy (stageIdentityQArm R n)).trans
        (classifyingSpaceUniversalHomotopy (stageZeroQArm R n)).symm) (t,z) := by
  change classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ)
      (((classifyingSpaceUniversalHomotopy (stageIdentityArm R n)).trans
        (classifyingSpaceUniversalHomotopy (stageZeroArm R n)).symm) (t,z)) = _
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (universalHomotopy_whiskerRight (stageIdentityArm R n)
      (localizedExtensionProjection Rᵐᵒᵖ) _ z).symm
  · exact (universalHomotopy_whiskerRight (stageZeroArm R n)
      (localizedExtensionProjection Rᵐᵒᵖ) _ z).symm

/-- The actual source-slide return loop, with the unchanged stored and denominator paths. -/
def universalStageReturnLoop (n : ℕ) :=
  HomotopyFiber.contractionReturnLoop
    (classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
      (exactStructure Rᵐᵒᵖ).kBasepoint (stageOriginalFiberMap R n)
      (classifyingSpacePoint
        ((stageDenominator R n).obj (exactStructure Rᵐᵒᵖ).extensionTotalPoint))
      (universalStageSourceContraction R n) (denominatorZeroPath R n)

/-- The unchanged native stage comparison is homotopic to right normalization of its actual
return family. -/
def nativeUniversalStageReturnHomotopy (n : ℕ) :
    ((completionToOriginalQLoops Rᵐᵒᵖ
        ((StableCompletion.stageFunctor R n).obj (stageVertex R n))).comp
      (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n))).Homotopy
        (Automorphism.rightNormalizedLoopMap (universalStageReturnLoop R n)
          (classifyingSpacePoint (stageVertex R n))) := by
  letI : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory Rᵐᵒᵖ)) :=
    localizedExtension_classifyingSpace_contractible Rᵐᵒᵖ
  let h := stageOriginalFiberMap R n
  let z₀ := classifyingSpacePoint (stageVertex R n)
  have J := HomotopyFiber.inverseReturnNormalizationHomotopy
    (classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
      (exactStructure Rᵐᵒᵖ).kBasepoint h
      (classifyingSpacePoint
        ((stageDenominator R n).obj (exactStructure Rᵐᵒᵖ).extensionTotalPoint))
      (universalStageSourceContraction R n) (denominatorZeroPath R n) z₀
  have hz : h z₀ = completionQFiberPoint Rᵐᵒᵖ
      ((StableCompletion.stageFunctor R n).obj (stageVertex R n)) := by
    change completionToOriginalQHomotopyFiber Rᵐᵒᵖ
      (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n) z₀) = _
    rw [classifyingSpaceMapUniversal_point]
    rfl
  change (loopReversal.comp
    ((HomotopyFiber.loopEquivOfContractibleSourcePath _
      (completionQFiberPoint Rᵐᵒᵖ _).val.1 _
      (HomotopyFiber.toPath _ _ (completionQFiberPoint Rᵐᵒᵖ _))).invFun.comp h)).Homotopy _
  rw [← hz]
  exact J

/-- The original native identity-entry projection is exactly the power identity-extension
projection. -/
theorem stageIdentityProjection_eq (n : ℕ) :
    StableCompletion.stageFunctor R n ⋙
      (completionIdentityEntry Rᵐᵒᵖ ⋙ localizedExtensionProjection Rᵐᵒᵖ) =
      stageCore R n ⋙ ((exactStructure Rᵐᵒᵖ).identityExtensionFunctor ⋙
        (exactStructure Rᵐᵒᵖ).extensionProjection) := by
  rw [← CategoryTheory.Functor.assoc, stageIdentity_fixedDenominator]
  simp only [CategoryTheory.Functor.assoc, fixedDenominatorExtension_projection, stageCore]

/-- The original inverse-quotient transformation restricted along the native stage functor. -/
def stageInverseQuotientCone (n : ℕ) :=
  Functor.whiskerLeft (StableCompletion.stageFunctor R n)
    (completionIdentityProjectionIsoZero Rᵐᵒᵖ).inv

/-- The original inverse identity-quotient transformation along the actual power core. -/
def stageCoreInverseQuotientCone (n : ℕ) :=
  Functor.whiskerLeft (stageCore R n)
    (exactStructure Rᵐᵒᵖ).identityExtensionProjectionIsoZero.inv

/-- The two actual inverse-quotient transformations agree under the exact endpoint functor
equality. -/
theorem stageInverseQuotientCone_eq (n : ℕ) :
    stageInverseQuotientCone R n ≫ eqToHom (stageIdentityProjection_eq R n) =
      stageCoreInverseQuotientCone R n := by
  apply NatTrans.ext
  funext j
  simp only [NatTrans.comp_app, eqToHom_app]
  change _ ≫ eqToHom (rfl : _ = _) = _
  rw [eqToHom_refl, Category.comp_id]
  rfl

/-- The reversed stored native fiber path is pointwise the original power-core inverse-quotient
track. -/
theorem originalStageInversePath_core (n : ℕ) (z : MatrixStageSpace R n) (t : unitInterval) :
    (originalStageFiberPath R n z).symm t =
      classifyingSpaceUniversalHomotopy
        (exactStructure Rᵐᵒᵖ).identityExtensionProjectionIsoZero.inv
          (t,classifyingSpaceMapUniversal (stageCore R n) z) := by
  change originalStageFiberPath R n z (unitInterval.symm t) = _
  rw [originalStageFiberPath_apply, unitInterval.symm_symm]
  have h₁ := universalHomotopy_whiskerLeft (StableCompletion.stageFunctor R n)
    (completionIdentityProjectionIsoZero Rᵐᵒᵖ).inv t z
  have h₂ := universalHomotopy_whiskerLeft (stageCore R n)
    (exactStructure Rᵐᵒᵖ).identityExtensionProjectionIsoZero.inv t z
  have hc := universalTransformation_congr rfl (stageIdentityProjection_eq R n)
    (stageInverseQuotientCone R n) (stageCoreInverseQuotientCone R n)
    (by simpa only [eqToHom_refl, Category.id_comp] using stageInverseQuotientCone_eq R n) t z
  exact h₁.symm.trans (hc.trans h₂)

/-- The actual localized projection forgets the unchanged fixed denominator on each original
arrow. -/
lemma stageDenominator_projection_map (n : ℕ)
    {X Y : (exactStructure Rᵐᵒᵖ).ExtensionTotal} (f : X ⟶ Y) :
    (localizedExtensionProjection Rᵐᵒᵖ).map ((stageDenominator R n).map f) =
      (exactStructure Rᵐᵒᵖ).extensionProjection.map f := by
  change (fixedDenominatorExtension Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) ⋙
    localizedExtensionProjection Rᵐᵒᵖ).map f = _
  have h := CategoryTheory.Functor.congr_hom
    (fixedDenominatorExtension_projection Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n)) f
  simpa only [CategoryTheory.Functor.comp_map, eqToHom_refl,
    Category.id_comp, Category.comp_id] using h

/-- Projection of each fixed-denominator extension diagram is its original extension
projection. -/
lemma stageProjectedDiagram (n : ℕ)
    (G : (exactStructure Rᵐᵒᵖ).ExtensionTotal ⥤ (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    ((stageExtension R n ⋙ G) ⋙ stageDenominator R n) ⋙
      localizedExtensionProjection Rᵐᵒᵖ =
      stageCore R n ⋙ (((exactStructure Rᵐᵒᵖ).identityExtensionFunctor ⋙ G) ⋙
        (exactStructure Rᵐᵒᵖ).extensionProjection) := by
  change (((stageCore R n ⋙ (exactStructure Rᵐᵒᵖ).identityExtensionFunctor) ⋙ G) ⋙
    fixedDenominatorExtension Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n)) ⋙ _ = _
  simp only [CategoryTheory.Functor.assoc, fixedDenominatorExtension_projection]

/-- The original projected contraction transformation agrees under the exact endpoint functor
equalities. -/
lemma stageProjectedArm_congr (n : ℕ)
    {F G : (exactStructure Rᵐᵒᵖ).ExtensionTotal ⥤ (exactStructure Rᵐᵒᵖ).ExtensionTotal}
    (α : F ⟶ G) :
    Functor.whiskerRight (Functor.whiskerRight (Functor.whiskerLeft (stageExtension R n) α)
      (stageDenominator R n)) (localizedExtensionProjection Rᵐᵒᵖ) ≫
        eqToHom (stageProjectedDiagram R n G) =
      eqToHom (stageProjectedDiagram R n F) ≫
        Functor.whiskerLeft (stageCore R n)
          (Functor.whiskerRight
            (Functor.whiskerLeft (exactStructure Rᵐᵒᵖ).identityExtensionFunctor α)
            (exactStructure Rᵐᵒᵖ).extensionProjection) := by
  apply NatTrans.ext
  funext j
  simp only [NatTrans.comp_app, eqToHom_app]
  change _ ≫ eqToHom (rfl : _ = _) = eqToHom (rfl : _ = _) ≫ _
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
  exact stageDenominator_projection_map R n (α.app ((stageExtension R n).obj j))

/-- The entire projected stage arm is the original power-core arm family. -/
theorem stageProjectedArm_core (n : ℕ)
    {F G : (exactStructure Rᵐᵒᵖ).ExtensionTotal ⥤ (exactStructure Rᵐᵒᵖ).ExtensionTotal}
    (α : F ⟶ G) (t : unitInterval) (z : MatrixStageSpace R n) :
    classifyingSpaceUniversalHomotopy
      (Functor.whiskerRight (Functor.whiskerRight (Functor.whiskerLeft (stageExtension R n) α)
        (stageDenominator R n)) (localizedExtensionProjection Rᵐᵒᵖ)) (t,z) =
      classifyingSpaceUniversalHomotopy
        (Functor.whiskerRight
          (Functor.whiskerLeft (exactStructure Rᵐᵒᵖ).identityExtensionFunctor α)
          (exactStructure Rᵐᵒᵖ).extensionProjection)
        (t,classifyingSpaceMapUniversal (stageCore R n) z) := by
  exact (universalTransformation_congr (stageProjectedDiagram R n F)
    (stageProjectedDiagram R n G) _ _ (stageProjectedArm_congr R n α) t z).trans
      (universalHomotopy_whiskerLeft (stageCore R n) _ t z)

/-- The original denominator-zero pair as a constant diagram on the finite stage. -/
def stageConstantPair (n : ℕ) : StableGeneralLinear.finiteCategory R n ⥤
    GroupCompletionCategory Rᵐᵒᵖ :=
  (Functor.const _).obj (denominatorZeroPair R n)

/-- The unchanged original inverse-quotient transformation at the constant denominator-zero
pair. -/
def stageConstantInverseCone (n : ℕ) :=
  Functor.whiskerLeft (stageConstantPair R n) (completionIdentityProjectionIsoZero Rᵐᵒᵖ).inv

/-- The canonical zero-quotient inverse along the actual power-core diagram. -/
def stageCoreConstantInverseCone (n : ℕ) :=
  Functor.whiskerLeft (stageCore R n)
    (Automorphism.constantIdentityProjectionIso (exactStructure Rᵐᵒᵖ)).inv

/-- The constant native projection is exactly the original zero-extension quotient diagram. -/
theorem stageConstantProjection_eq (n : ℕ) :
    stageConstantPair R n ⋙
      (completionIdentityEntry Rᵐᵒᵖ ⋙ localizedExtensionProjection Rᵐᵒᵖ) =
      stageCore R n ⋙ (((exactStructure Rᵐᵒᵖ).identityExtensionFunctor ⋙
        (Functor.const (exactStructure Rᵐᵒᵖ).ExtensionTotal).obj
          (exactStructure Rᵐᵒᵖ).extensionTotalPoint) ⋙
        (exactStructure Rᵐᵒᵖ).extensionProjection) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (localizedExtensionProjection Rᵐᵒᵖ).map
    ((completionIdentityEntry Rᵐᵒᵖ).map (𝟙 _)) =
      (exactStructure Rᵐᵒᵖ).extensionProjection.map (𝟙 _)
  rw [(completionIdentityEntry Rᵐᵒᵖ).map_id,
    (localizedExtensionProjection Rᵐᵒᵖ).map_id,
    (exactStructure Rᵐᵒᵖ).extensionProjection.map_id]
  rfl

/-- The two zero-quotient inverse transformations agree under that exact diagram equality. -/
theorem stageConstantInverseCone_eq (n : ℕ) :
    stageConstantInverseCone R n ≫ eqToHom (stageConstantProjection_eq R n) =
      stageCoreConstantInverseCone R n := by
  apply NatTrans.ext
  funext j
  simp only [NatTrans.comp_app, eqToHom_app]
  change _ ≫ eqToHom (rfl : _ = _) = _
  rw [eqToHom_refl, Category.comp_id]
  rfl

/-- The original denominator path is pointwise the reverse canonical zero-quotient family. -/
theorem denominatorZeroInversePath_core (n : ℕ) (z : MatrixStageSpace R n) (t : unitInterval) :
    (denominatorZeroPath R n).symm t =
      classifyingSpaceUniversalHomotopy
        (Automorphism.constantIdentityProjectionIso (exactStructure Rᵐᵒᵖ)).inv
          (t,classifyingSpaceMapUniversal (stageCore R n) z) := by
  have hv : (denominatorZeroPath R n).symm t =
      classifyingSpaceUniversalHomotopy (completionIdentityProjectionIsoZero Rᵐᵒᵖ).inv
        (t,classifyingSpacePoint (denominatorZeroPair R n)) := by
    rw [classifyingSpaceUniversalHomotopy_vertex_track]
    change (classifyingSpacePath ((completionIdentityProjectionIsoZero Rᵐᵒᵖ).inv.app
      (denominatorZeroPair R n))) (unitInterval.symm (unitInterval.symm t)) = _
    rw [unitInterval.symm_symm]
  have h₁ := universalHomotopy_whiskerLeft (stageConstantPair R n)
    (completionIdentityProjectionIsoZero Rᵐᵒᵖ).inv t z
  have hm : classifyingSpaceMapUniversal (stageConstantPair R n) z =
      classifyingSpacePoint (denominatorZeroPair R n) := by
    change classifyingSpaceMapUniversal ((Functor.const _).obj (denominatorZeroPair R n)) z = _
    rw [classifyingSpaceMapUniversal_const]
    rfl
  rw [hm] at h₁
  have h₂ := universalHomotopy_whiskerLeft (stageCore R n)
    (Automorphism.constantIdentityProjectionIso (exactStructure Rᵐᵒᵖ)).inv t z
  have hc := universalTransformation_congr rfl (stageConstantProjection_eq R n)
    (stageConstantInverseCone R n) (stageCoreConstantInverseCone R n)
    (by simpa only [eqToHom_refl, Category.id_comp] using stageConstantInverseCone_eq R n) t z
  exact hv.trans (h₁.symm.trans (hc.trans h₂))

/-- The projected universal source contraction is the original pair of power-core Q arms. -/
theorem projectedUniversalStageContraction_core (n : ℕ) (t : unitInterval)
    (z : MatrixStageSpace R n) :
    classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ)
      (universalStageSourceContraction R n (t,z)) =
      ((Automorphism.identityArmHomotopy (exactStructure Rᵐᵒᵖ)).trans
        (Automorphism.zeroArmHomotopy (exactStructure Rᵐᵒᵖ)).symm)
        (t,classifyingSpaceMapUniversal (stageCore R n) z) := by
  rw [projectedUniversalStageContraction,
    ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact stageProjectedArm_core R n
      (Subdivision.identityToInitialRaise (exactStructure Rᵐᵒᵖ).inflationZeroIsInitial) _ z
  · exact stageProjectedArm_core R n
      (Subdivision.constantToInitialRaise (exactStructure Rᵐᵒᵖ).inflationZeroIsInitial) _ z

/-- The native stored-path return family is pointwise the original categorical four-arm family. -/
theorem universalStageReturnLoop_eq_coreReturn (n : ℕ) :
    universalStageReturnLoop R n =
      (Automorphism.coreReturnLoopMap (exactStructure Rᵐᵒᵖ)).comp
        (classifyingSpaceMapUniversal (stageCore R n)) := by
  ext z t
  let E := exactStructure Rᵐᵒᵖ
  let p := classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ)
  let H := universalStageSourceContraction R n
  let Γ := HomotopyFiber.toPath p E.kBasepoint (stageOriginalFiberMap R n z)
  let w := classifyingSpaceMapUniversal (stageCore R n) z
  have hΓ (s : unitInterval) : Γ.symm s = Automorphism.inverseQuotientHomotopy E (s,w) :=
    originalStageInversePath_core R n z s
  have hΔ (s : unitInterval) : ((H.evalAt z).map p.continuous) s =
      ((Automorphism.identityArmHomotopy E).trans (Automorphism.zeroArmHomotopy E).symm)
        (s,w) := projectedUniversalStageContraction_core R n s z
  have hγ (s : unitInterval) : denominatorZeroPath R n s =
      (Automorphism.constantInverseQuotientHomotopy E).symm (s,w) := by
    have h := denominatorZeroInversePath_core R n z (unitInterval.symm s)
    change denominatorZeroPath R n (unitInterval.symm (unitInterval.symm s)) = _ at h
    rw [unitInterval.symm_symm] at h
    exact h
  change ((((H.evalAt z).symm.map p.continuous).trans Γ).symm.trans
    (denominatorZeroPath R n)) t = _
  rw [Path.trans_symm, Path.map_symm, Path.symm_symm]
  change ((Γ.symm.trans ((H.evalAt z).map p.continuous)).trans
    (denominatorZeroPath R n)) t =
      (((Automorphism.inverseQuotientHomotopy E).trans
        ((Automorphism.identityArmHomotopy E).trans
          (Automorphism.zeroArmHomotopy E).symm)).trans
            (Automorphism.constantInverseQuotientHomotopy E).symm) (t,w)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hΓ _
    · exact hΔ _
  · exact hγ _

/-- The actual stage return family is homotopic to one reversal of the zero-first core loop
map. -/
def universalStageReturnCoreHomotopy (n : ℕ) :
    (universalStageReturnLoop R n).Homotopy
      ((loopReversal.comp (Automorphism.universalCoreLoopMap (exactStructure Rᵐᵒᵖ))).comp
        (classifyingSpaceMapUniversal (stageCore R n))) :=
  ((Automorphism.coreReturnLoopPositiveHomotopy (exactStructure Rᵐᵒᵖ)).compContinuousMap
    (classifyingSpaceMapUniversal (stageCore R n))).cast
      (universalStageReturnLoop_eq_coreReturn R n).symm rfl

/-- The original native completion-to-Q loop comparison on this actual finite stage. -/
def nativeStageLoopMap (n : ℕ) :=
  (completionToOriginalQLoops Rᵐᵒᵖ
    ((StableCompletion.stageFunctor R n).obj (stageVertex R n))).comp
      (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n))

/-- The zero-first universal Q-cone loop map of the actual finite power action. -/
def stageCoreLoopMap (n : ℕ) :=
  (Automorphism.universalCoreLoopMap (exactStructure Rᵐᵒᵖ)).comp
    (classifyingSpaceMapUniversal (stageCore R n))

open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies in
/-- The actual constant stage-vertex row and power-action row commute through
biproduct braiding, retaining the whole vertex track. -/
def stageCoreLoopCommutation (n : ℕ) :
    (⟨fun z => (stageCoreLoopMap R n (classifyingSpacePoint (stageVertex R n))).trans
      (stageCoreLoopMap R n z), by fun_prop⟩ :
        C(MatrixStageSpace R n, Path (exactStructure Rᵐᵒᵖ).kBasepoint
          (exactStructure Rᵐᵒᵖ).kBasepoint)).Homotopy
      ⟨fun z => (stageCoreLoopMap R n z).trans
        (stageCoreLoopMap R n (classifyingSpacePoint (stageVertex R n))), by fun_prop⟩ := by
  let E := exactStructure Rᵐᵒᵖ
  let L : StableGeneralLinear.finiteCategory R n ⥤ IsoCategory Rᵐᵒᵖ :=
    (Functor.const _).obj ((stageCore R n).obj (stageVertex R n))
  have hrow (B : StableGeneralLinear.finiteCategory R n ⥤ IsoCategory Rᵐᵒᵖ) :
      ConePair.naturalPair (zeroCone E B) (fullCone E B) =
        (Automorphism.universalCoreLoopMap E).comp (classifyingSpaceMapUniversal B) := by
    ext z t
    change (((ConePair.realizedCone (zeroCone E B)).evalAt z).trans
      ((ConePair.realizedCone (fullCone E B)).evalAt z).symm) t =
      (((ConePair.realizedCone (Automorphism.zeroCone E)).evalAt
        (classifyingSpaceMapUniversal B z)).trans
        ((ConePair.realizedCone (Automorphism.fullCone E)).evalAt
          (classifyingSpaceMapUniversal B z)).symm) t
    simp only [Path.trans_apply, Path.symm_apply]
    split_ifs
    · exact universalHomotopy_whiskerLeft B (Automorphism.zeroCone E) _ z
    · exact universalHomotopy_whiskerLeft B (Automorphism.fullCone E) _ z
  have hconst : (Automorphism.universalCoreLoopMap E).comp
      (classifyingSpaceMapUniversal L) =
        ContinuousMap.const (MatrixStageSpace R n)
          (stageCoreLoopMap R n (classifyingSpacePoint (stageVertex R n))) := by
    ext z t
    change Automorphism.universalCoreLoopMap E
      (classifyingSpaceMapUniversal ((Functor.const _).obj
        ((stageCore R n).obj (stageVertex R n))) z) t =
      Automorphism.universalCoreLoopMap E
        (classifyingSpaceMapUniversal (stageCore R n)
          (classifyingSpacePoint (stageVertex R n))) t
    rw [classifyingSpaceMapUniversal_const, classifyingSpaceMapUniversal_point]
    rfl
  have H := coreLoopCommutation E L (stageCore R n)
  rw [hrow L, hrow (stageCore R n), hconst] at H
  exact H

/-- Actual finite-stage braiding identifies the two original normalization orders,
retaining both prescribed caps. -/
theorem stageCoreLoop_normalizationOrder (n : ℕ)
    (a : HomotopyGroup.Pi 1 (MatrixStageSpace R n) (classifyingSpacePoint (stageVertex R n))) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv
        (Automorphism.rightNormalizationPath (loopReversal.comp (stageCoreLoopMap R n))
          (classifyingSpacePoint (stageVertex R n))) 0
        (piMap 0
          (Automorphism.rightNormalizedLoopMap (loopReversal.comp (stageCoreLoopMap R n))
            (classifyingSpacePoint (stageVertex R n))) rfl a)) =
      (loopShiftMulEquiv 0).symm
        (pathTransportMulEquiv
          (Automorphism.positiveNormalizationPath (stageCoreLoopMap R n)
            (classifyingSpacePoint (stageVertex R n))) 0
          (piMap 0
            (Automorphism.positiveNormalizedLoopMap (stageCoreLoopMap R n)
              (classifyingSpacePoint (stageVertex R n))) rfl a)) := by
  let f := stageCoreLoopMap R n
  let z := classifyingSpacePoint (stageVertex R n)
  let l : C(MatrixStageSpace R n, Path (exactStructure Rᵐᵒᵖ).kBasepoint
      (exactStructure Rᵐᵒᵖ).kBasepoint) :=
    ⟨fun w => (f w).symm.trans (f z),
      Path.continuous_trans.comp
        ((Path.continuous_symm.comp f.continuous).prodMk continuous_const)⟩
  let r : C(MatrixStageSpace R n, Path (exactStructure Rᵐᵒᵖ).kBasepoint
      (exactStructure Rᵐᵒᵖ).kBasepoint) :=
    ⟨fun w => (f z).trans (f w).symm,
      Path.continuous_trans.comp
        (continuous_const.prodMk (Path.continuous_symm.comp f.continuous))⟩
  have hl : Automorphism.rightNormalizedLoopMap (loopReversal.comp f) z = l := by
    ext w : 1
    change (f w).symm.trans (f z).symm.symm = (f w).symm.trans (f z)
    rw [Path.symm_symm]
  have hr : Automorphism.positiveNormalizedLoopMap f z = r := by
    ext w : 1
    change ((f w).trans (f z).symm).symm = (f z).trans (f w).symm
    rw [Path.trans_symm, Path.symm_symm]
  let γ : Path (l z) (Path.refl (exactStructure Rᵐᵒᵖ).kBasepoint) :=
    (Automorphism.rightNormalizationPath (loopReversal.comp f) z).cast
      (congrArg (fun g => g z) hl).symm rfl
  let δ : Path (r z) (Path.refl (exactStructure Rᵐᵒᵖ).kBasepoint) :=
    (Automorphism.positiveNormalizationPath f z).cast
      (congrArg (fun g => g z) hr).symm rfl
  have hleft := DFunLike.congr_fun (piOne_homotopy_corrected
    ((ContinuousMap.Homotopy.refl l).cast hl.symm rfl)
    (Automorphism.rightNormalizationPath (loopReversal.comp f) z) γ
    (Automorphism.loopComponent_piOne_mul_comm
      (Path.refl (exactStructure Rᵐᵒᵖ).kBasepoint))) a
  have hright := DFunLike.congr_fun (piOne_homotopy_corrected
    ((ContinuousMap.Homotopy.refl r).cast rfl hr.symm) δ
    (Automorphism.positiveNormalizationPath f z)
    (Automorphism.loopComponent_piOne_mul_comm
      (Path.refl (exactStructure Rᵐᵒᵖ).kBasepoint))) a
  have horder := Topology.loopFamily_normalizationOrder f z
    (stageCoreLoopCommutation R n) γ δ a
  exact (congrArg (loopShiftMulEquiv 0).symm hleft).trans
    (horder.trans (congrArg (loopShiftMulEquiv 0).symm hright))

/-- The unchanged native stage map is homotopic to right normalization of the full-first core
family. -/
def nativeStageCoreHomotopy (n : ℕ) :
    (nativeStageLoopMap R n).Homotopy
      (Automorphism.rightNormalizedLoopMap (loopReversal.comp (stageCoreLoopMap R n))
        (classifyingSpacePoint (stageVertex R n))) :=
  (nativeUniversalStageReturnHomotopy R n).trans
    (Automorphism.rightNormalizedHomotopy (universalStageReturnCoreHomotopy R n)
      (classifyingSpacePoint (stageVertex R n)))

/-- The original prescribed completion correction path with its exact stage-vertex equality
inserted. -/
def nativeStageLoopBasepointPath (n : ℕ) :
    Path (nativeStageLoopMap R n (classifyingSpacePoint (stageVertex R n)))
      (Path.refl (exactStructure Rᵐᵒᵖ).kBasepoint) :=
  (completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ
    ((StableCompletion.stageFunctor R n).obj (stageVertex R n))).cast
      (congrArg (completionToOriginalQLoops Rᵐᵒᵖ
        ((StableCompletion.stageFunctor R n).obj (stageVertex R n)))
        (classifyingSpaceMapUniversal_point (StableCompletion.stageFunctor R n) (stageVertex R n)))
      rfl

/-- The actual native corrected stage class is the positive normalized core class, retaining
both caps. -/
theorem nativeStageLoop_positiveClass (n : ℕ)
    (a : HomotopyGroup.Pi 1 (MatrixStageSpace R n) (classifyingSpacePoint (stageVertex R n))) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv (nativeStageLoopBasepointPath R n) 0
        (piMap 0 (nativeStageLoopMap R n) rfl a)) =
      (loopShiftMulEquiv 0).symm
        (pathTransportMulEquiv
          (Automorphism.positiveNormalizationPath (stageCoreLoopMap R n)
            (classifyingSpacePoint (stageVertex R n))) 0
          (piMap 0
            (Automorphism.positiveNormalizedLoopMap (stageCoreLoopMap R n)
              (classifyingSpacePoint (stageVertex R n))) rfl a)) := by
  have h := DFunLike.congr_fun (piOne_homotopy_corrected (nativeStageCoreHomotopy R n)
    (nativeStageLoopBasepointPath R n)
    (Automorphism.rightNormalizationPath (loopReversal.comp (stageCoreLoopMap R n))
      (classifyingSpacePoint (stageVertex R n)))
    (Automorphism.loopComponent_piOne_mul_comm (Path.refl (exactStructure Rᵐᵒᵖ).kBasepoint))) a
  exact (congrArg (loopShiftMulEquiv 0).symm h).trans
    (stageCoreLoop_normalizationOrder R n a)

/-- An exact source-endpoint equality preserves the original path-corrected homotopy map. -/
private lemma corrected_cast_source {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y y' : Y} (h : f x = y) (γ : Path y y')
    (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport (γ.cast h rfl) n (HomotopyGroup.map f rfl a) =
      pathTransport γ n (HomotopyGroup.map f h a) := by
  subst y
  rfl

/-- The original positive completion equivalence has the displayed positive finite-stage core
value. -/
theorem completionStage_positiveClass (n : ℕ)
    (a : HomotopyGroup.Pi 1 (MatrixStageSpace R n) (classifyingSpacePoint (stageVertex R n))) :
    completionPositiveKEquiv Rᵐᵒᵖ ((StableCompletion.stageFunctor R n).obj (stageVertex R n)) 0
      (piMap 0 (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n))
        (classifyingSpaceMapUniversal_point
          (StableCompletion.stageFunctor R n) (stageVertex R n)) a) =
      (loopShiftMulEquiv 0).symm
        (pathTransportMulEquiv
          (Automorphism.positiveNormalizationPath (stageCoreLoopMap R n)
            (classifyingSpacePoint (stageVertex R n))) 0
          (piMap 0
            (Automorphism.positiveNormalizedLoopMap (stageCoreLoopMap R n)
              (classifyingSpacePoint (stageVertex R n))) rfl a)) := by
  let S := classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n)
  let U := (StableCompletion.stageFunctor R n).obj (stageVertex R n)
  let L := completionToOriginalQLoops Rᵐᵒᵖ U
  let hS := classifyingSpaceMapUniversal_point (StableCompletion.stageFunctor R n) (stageVertex R n)
  let γ := completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ U
  change (loopShiftMulEquiv 0).symm
    (pathTransport γ 1 (HomotopyGroup.map L rfl (HomotopyGroup.map S hS a))) = _
  rw [← HomotopyGroup.map_comp S hS L rfl a]
  have h := corrected_cast_source (L.comp S) (congrArg L hS) γ 1 a
  exact (congrArg (loopShiftMulEquiv 0).symm h.symm).trans (nativeStageLoop_positiveClass R n a)

/-- The original realized finite matrix edge in the actual finite-stage fundamental group. -/
def finiteMatrixPiOne (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    HomotopyGroup.Pi 1 (MatrixStageSpace R n) (classifyingSpacePoint (stageVertex R n)) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    (FundamentalGroup.fromPath ⟦classifyingSpacePath
      (AsSmall.up.map (SingleObj.toEnd (Matrix.GeneralLinearGroup (Fin n) R) g).asHom)⟧)

/-- The actual stage functor sends the finite edge to its unchanged native power-action edge. -/
theorem finiteMatrixPiOne_image (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    piMap 0 (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n))
      (classifyingSpaceMapUniversal_point (StableCompletion.stageFunctor R n) (stageVertex R n))
      (finiteMatrixPiOne R n g) =
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (FundamentalGroup.fromPath
        ⟦classifyingSpacePath (StableCompletion.stageAction R n g).asHom⟧) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n))
      (classifyingSpaceMapUniversal_point (StableCompletion.stageFunctor R n) (stageVertex R n))
      (finiteMatrixPiOne R n g)) = _
  erw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply]
  rw [FundamentalGroup.mapOfEq_apply]
  apply End.ext
  exact congrArg Path.Homotopic.Quotient.mk
    (classifyingSpaceMapUniversal_path_cast (StableCompletion.stageFunctor R n)
      (AsSmall.up.map (SingleObj.toEnd (Matrix.GeneralLinearGroup (Fin n) R) g).asHom))

/-- The original unit-arrow path from the monoidal-unit pair to the equal-power pair. -/
def matrixUnitPath (n : ℕ) :
    Path (classifyingSpacePoint (StableCompletion.stageObject R 0))
      (classifyingSpacePoint (StableCompletion.stageObject R n)) :=
  classifyingSpacePath (GroupCompletion.Localization.unitArrow
    (𝟙 (rankOnePower Rᵐᵒᵖ n)))

/-- The unchanged completed numerator is the actual power-action loop transported along the
inverse unit path. -/
theorem numeratorPiOne_eq_transport (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (classifyingGroupoidCompletionMap (StableCompletion.Completion R)
        (StableCompletion.stageObject R 0)
        (GroupCompletion.Localization.numeratorLoop (StableFree.powerEndEquiv R n g).asHom)) =
    pathTransport (matrixUnitPath R n).symm 1
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (FundamentalGroup.fromPath
          ⟦classifyingSpacePath (StableCompletion.stageAction R n g).asHom⟧)) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [MulEquiv.apply_symm_apply, piOneEquivFundamentalGroup_pathTransport,
    MulEquiv.apply_symm_apply]
  apply End.ext
  let C := StableCompletion.Completion R
  let Q := (⊤ : MorphismProperty C).Q
  let L := classifyingGroupoidCompletionFunctor C
  let u := GroupCompletion.Localization.unitArrow (𝟙 (rankOnePower Rᵐᵒᵖ n))
  let a := (StableCompletion.stageAction R n g).asHom
  have hu : L.map (Q.map u) = Path.Homotopic.Quotient.mk (classifyingSpacePath u) := by
    change ((⊤ : MorphismProperty C).Q ⋙ classifyingGroupoidCompletionFunctor C).map u =
      (classifyingFundamentalGroupoidFunctor C).map u
    have h := CategoryTheory.Functor.congr_hom (toClassifyingGroupoidCompletionFunctor C) u
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h
  have ha : L.map (Q.map a) = Path.Homotopic.Quotient.mk (classifyingSpacePath a) := by
    change ((⊤ : MorphismProperty C).Q ⋙ classifyingGroupoidCompletionFunctor C).map a =
      (classifyingFundamentalGroupoidFunctor C).map a
    have h := CategoryTheory.Functor.congr_hom (toClassifyingGroupoidCompletionFunctor C) a
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h
  change L.map (Q.map u ≫ Q.map a ≫ inv (Q.map u)) = _
  rw [L.map_comp, L.map_comp, L.map_inv, ← Groupoid.inv_eq_inv, hu, ha]
  let cp : FundamentalGroupoid.mk (classifyingSpacePoint (StableCompletion.stageObject R 0)) ⟶
      FundamentalGroupoid.mk (classifyingSpacePoint (StableCompletion.stageObject R n)) :=
    Path.Homotopic.Quotient.mk (matrixUnitPath R n)
  let ca : Path.Homotopic.Quotient
      (classifyingSpacePoint (StableCompletion.stageObject R n))
      (classifyingSpacePoint (StableCompletion.stageObject R n)) :=
    Path.Homotopic.Quotient.mk (classifyingSpacePath a)
  change cp ≫ ca ≫ Groupoid.inv cp = Groupoid.inv (Groupoid.inv cp) ≫ ca ≫ Groupoid.inv cp
  simp only [Groupoid.inv_eq_inv, CategoryTheory.IsIso.inv_inv]

/-- The canonical quotient-Q matrix value is its original finite-stage completion value. -/
theorem elementaryProjectiveKOneEquiv_matrix_stage (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableCompletion.elementaryProjectiveKOneEquiv R
      (StableGeneralLinear.quotientMap R (StableGeneralLinear.of R n g)) =
    completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R n) 0
      (piMap 0 (classifyingSpaceMapUniversal (StableCompletion.stageFunctor R n))
        (classifyingSpaceMapUniversal_point (StableCompletion.stageFunctor R n) (stageVertex R n))
        (finiteMatrixPiOne R n g)) := by
  exact (StableCompletion.elementaryProjectiveKOneEquiv_matrix_numerator R n g).trans
    ((congrArg (completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0) 0)
      (numeratorPiOne_eq_transport R n g)).trans
        ((completionPositiveKEquiv_pathTransport Rᵐᵒᵖ (matrixUnitPath R n).symm 0 _).trans
          (congrArg (completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R n) 0)
            (finiteMatrixPiOne_image R n g).symm)))

/-- The canonical quotient-Q comparison sends each original matrix to its positive universal
core class. -/
theorem elementaryProjectiveKOneEquiv_matrix_positiveCore (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableCompletion.elementaryProjectiveKOneEquiv R
      (StableGeneralLinear.quotientMap R (StableGeneralLinear.of R n g)) =
      (loopShiftMulEquiv 0).symm
        (pathTransportMulEquiv
          (Automorphism.positiveNormalizationPath (stageCoreLoopMap R n)
            (classifyingSpacePoint (stageVertex R n))) 0
          (piMap 0
            (Automorphism.positiveNormalizedLoopMap (stageCoreLoopMap R n)
              (classifyingSpacePoint (stageVertex R n))) rfl (finiteMatrixPiOne R n g))) :=
  (elementaryProjectiveKOneEquiv_matrix_stage R n g).trans
    (completionStage_positiveClass R n (finiteMatrixPiOne R n g))

end ModuleCat.FiniteProjective
