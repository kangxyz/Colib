/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Quillen.Field.SymbolMarking.ScalarCube
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionStages
public import Colib.Topology.HomotopyFiber.HomotopyPiOneNaturality
public import Colib.KTheory.Quillen.ProjectiveCompletionBasepoint
public import Colib.Topology.HomotopyFiber.PeriodicConnecting
public import Colib.KTheory.MilnorK.QuillenComparison
public import Colib.KTheory.Quillen.Field.UpperModuleComparison
public import Colib.KTheory.Quillen.SmallModel.CommonAmbientNaturality
public import Colib.KTheory.Quillen.Map.CommonAmbient
public import Colib.KTheory.Quillen.LowDegreeScalarAction.FieldSymbols
public import Colib.Topology.ClassifyingSpace.UniverseNaturality

/-!
# Positive ordered Milnor symbols in the original Quillen K2 groups over a field

Positive ordered Milnor symbols in the original Quillen K2 groups over a field.

All comparisons retain the original maps and require only the stated hypotheses.
-/
/-! Adapted from `Quillen/KTheory/Field/PositiveSymbolMarking.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual completion maps, retained
axis caps and the two original signs are unchanged. The final comparison uses
the native common-ambient SmallModel map and literal upper SmallK, over every field. -/
@[expose] public section
noncomputable section

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup SSet
open scoped Topology unitInterval
universe u v
namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective StableCompletion
variable (F : Type u) [Field F]

/-- Only the original finite-stage target vertex is selected; its original map is retained. -/
def stageThreeQMap := completionToOriginalQLoops Fᵐᵒᵖ (stageObject F 3)

/-- The stage-three Q-loop map restricted to the zero component. -/
def zeroToStageThreeQLoops :=
  (stageThreeQMap F).comp (pathComponentInclusion (zeroPoint F))

/-- The original stable map into the stage-three Q-loop space. -/
def stableOriginalLoopMap := (zeroToStageThreeQLoops F).comp (stableZeroMap F)

/-- The stable classifying-space map of the rank-three diagonal representation. -/
def stableDiagonalSource : C(ClassifyingSpace (TorusSource F),
    ClassifyingSpace (SingleObj (StableGeneralLinear.Group F))) :=
  classifyingSpaceMapUniversal
    (((StableGeneralLinear.of F 3).comp (diagonalRepresentation F)).toFunctor)

theorem stableDiagonalSource_point :
    stableDiagonalSource F (classifyingSpacePoint (SingleObj.star _)) = stableBase F :=
  classifyingSpaceMapUniversal_point _ _

/-- The original common-universe realization homeomorphism is the actual universal up map. -/
theorem asSmallHomeomorph_eq_universal {C : Type u} [Category.{v} C] :
    (⟨asSmallClassifyingHomeomorph C,
      (asSmallClassifyingHomeomorph C).continuous⟩ : C(_, _)) =
    classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{0} C) := by
  apply DFunLike.coe_injective
  apply SSet.realization_ext
  intro n x t
  rw [classifyingSpaceMapUniversal_simplex]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm x) ≫
    SSet.toTop.map (asSmallNerveIso C).hom) ((SimplexCategory.toTopHomeo n).symm t) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (x ⋙ AsSmall.up))
        ((SimplexCategory.toTopHomeo n).symm t)
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

theorem stableDiagonalSource_stage :
    stableDiagonalSource F = (StableGeneralLinear.stageMap F 3).hom.comp
      (classifyingSpaceMapUniversal (diagonalRepresentation F).toFunctor) := by
  rw [stableDiagonalSource, StableGeneralLinear.stageMap, ← classifyingSpaceMapUniversal_eq,
    ← classifyingSpaceMapUniversal_comp]
  rfl

/-- The exact finite/stable comparison is used as a whole map homotopy. -/
def stableDiagonalStageHomotopy :
    ((stableOriginalLoopMap F).comp (stableDiagonalSource F)).Homotopy
      (nativeRankThreeLoopMap F) := by
  let H := (ContinuousMap.Homotopy.refl (stageThreeQMap F)).comp
    ((stableMap_stage F 3).some.compContinuousMap
      (classifyingSpaceMapUniversal (diagonalRepresentation F).toFunctor))
  refine H.cast ?_ ?_
  · rw [stableDiagonalSource_stage]
    rfl
  · rw [finiteCompletionMap, asSmallHomeomorph_eq_universal, ContinuousMap.comp_assoc,
      ← classifyingSpaceMapUniversal_comp]
    rfl

/-- The source torus mapped into the stable general linear classifying space. -/
def stableTorus (a b : Fˣ) := periodicPost (stableDiagonalSource F) (sourceTorus F a b)

theorem stableTorus_vertex (a b : Fˣ) :
    (stableTorus F a b).val (0,0) = stableBase F := by
  change stableDiagonalSource F (rawTorus F a b (0,0)) = _
  rw [rawTorus_zero_first, Path.source, stableDiagonalSource_point]

/-- All finite-stage, source, splitting and cap homotopies form one periodic native diagram. -/
def stableToScalarCube (a b : Fˣ) :
    Path (periodicPost (stableOriginalLoopMap F) (stableTorus F a b))
      (periodicOfCube (scalarLoopCube F a b)) :=
  (periodicPostHomotopy (stableDiagonalStageHomotopy F) (sourceTorus F a b)).trans
    (nativeToScalarCube F a b)

/-- Strict target base change retains the original stable-zero map. -/
theorem stableOriginalLoopMap_square :
    (zeroToStageThreeQLoops F).comp (stableZeroMap F) =
      (stableOriginalLoopMap F).comp (ContinuousMap.id _) := rfl

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup SSet
open scoped Topology unitInterval
universe u
namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective StableCompletion
variable (F : Type u) [Field F]

/-- The first diagonal is exactly the original rank-two torus matrix after one stabilization. -/
theorem diagonal_first_step (a : Fˣ) :
    diagonalRepresentation F (a,1) = StableGeneralLinear.step F 2 (StableSteinberg.hMatrix a) := by
  apply Units.ext
  rw [diagonalRepresentation_first]
  ext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp only [StableGeneralLinear.step_val_last, StableGeneralLinear.step_val_castSucc_last,
      StableGeneralLinear.step_val_last_castSucc, StableGeneralLinear.step_val_castSucc,
      StableSteinberg.hMatrix_val]
  · rfl
  · rename_i j
    fin_cases j <;> rfl
  · rename_i i
    fin_cases i <;> rfl
  · rename_i i j
    fin_cases i <;> fin_cases j <;> rfl

theorem diagonal_first_stable (a : Fˣ) :
    StableGeneralLinear.of F 3 (diagonalRepresentation F (a,1)) =
      StableSteinberg.toStableGeneralLinear F (StableSteinberg.h a) := by
  rw [diagonal_first_step, StableSteinberg.toStableGeneralLinear_h,
    ← StableGeneralLinear.transition_succ, StableGeneralLinear.of_transition]

/-- The elementary Weyl matrix in coordinates zero and two. -/
def w02Matrix (a : Fˣ) : Matrix.GeneralLinearGroup (Fin 3) F :=
  Matrix.GeneralLinearGroup.elementary (0 : Fin 3) 2 (by decide) (a : F) *
    Matrix.GeneralLinearGroup.elementary (2 : Fin 3) 0 (by decide) (-((a⁻¹ : Fˣ) : F)) *
      Matrix.GeneralLinearGroup.elementary (0 : Fin 3) 2 (by decide) (a : F)

theorem w02Matrix_val (a : Fˣ) :
    (w02Matrix F a).val = !![0,0,(a : F); 0,1,0; -((a⁻¹ : Fˣ) : F),0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w02Matrix, Units.val_mul, Matrix.GeneralLinearGroup.elementary_val,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single, Matrix.one_apply]

theorem diagonal_second_word (b : Fˣ) :
    diagonalRepresentation F (1,b) = w02Matrix F b * w02Matrix F (-1) := by
  apply Units.ext
  rw [diagonalRepresentation_second, Units.val_mul, w02Matrix_val, w02Matrix_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem diagonal_second_stable (b : Fˣ) :
    StableGeneralLinear.of F 3 (diagonalRepresentation F (1,b)) =
      StableSteinberg.toStableGeneralLinear F (StableSteinberg.h02 b) := by
  rw [diagonal_second_word]
  simp only [StableSteinberg.h02, StableSteinberg.w02, map_mul,
    StableSteinberg.toStableGeneralLinear_x, w02Matrix]

/-- The actual source edge maps to the actual stable matrix edge, with positive orientation. -/
theorem stableDiagonalSource_piOne (g : Fˣ × Fˣ) :
    piMap 0 (stableDiagonalSource F) (stableDiagonalSource_point F) (sourcePiOne F g) =
      GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)
        (StableGeneralLinear.of F 3 (diagonalRepresentation F g)) := by
  apply (HomotopyGroup.pi1MulEquivFundamentalGroup
    (x := classifyingSpacePoint (SingleObj.star (StableGeneralLinear.Group F)))).injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map (stableDiagonalSource F) (stableDiagonalSource_point F)
      (sourcePiOne F g)) = _
  erw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply]
  rw [FundamentalGroup.mapOfEq_apply]
  apply End.ext
  exact congrArg Path.Homotopic.Quotient.mk
    (classifyingSpaceMapUniversal_path_cast
      (((StableGeneralLinear.of F 3).comp (diagonalRepresentation F)).toFunctor)
        (SingleObj.toEnd _ g).asHom)

/-- Both torus axes retain the original ordered Steinberg diagonal markings. -/
theorem stableDiagonalSource_first_class (a : Fˣ) :
    piMap 0 (stableDiagonalSource F) (stableDiagonalSource_point F) (sourcePiOne F (a,1)) =
      stableFiberPiOneProjection F (steinbergToStableFiber F (StableSteinberg.h a)) := by
  rw [stableDiagonalSource_piOne, diagonal_first_stable]
  exact (DFunLike.congr_fun (steinbergToStableFiber_projection F) (StableSteinberg.h a)).symm

theorem stableDiagonalSource_second_class (b : Fˣ) :
    piMap 0 (stableDiagonalSource F) (stableDiagonalSource_point F) (sourcePiOne F (1,b)) =
      stableFiberPiOneProjection F (steinbergToStableFiber F (StableSteinberg.h02 b)) := by
  rw [stableDiagonalSource_piOne, diagonal_second_stable]
  exact (DFunLike.congr_fun (steinbergToStableFiber_projection F) (StableSteinberg.h02 b)).symm

/-- The based stable loop of a source unit pair. -/
def stableAxis (g : Fˣ × Fˣ) : Path (stableBase F) (stableBase F) :=
  ((sourceEdge F g).map (f := stableDiagonalSource F) (stableDiagonalSource F).continuous).cast
    (stableDiagonalSource_point F).symm (stableDiagonalSource_point F).symm

theorem stableTorus_first (a b : Fˣ) (t : unitInterval) :
    (stableTorus F a b).val (t,0) = stableAxis F (a,1) t := by
  change stableDiagonalSource F (rawTorus F a b (t,0)) = _
  rw [rawTorus_zero_second]
  rfl

theorem stableTorus_second (a b : Fˣ) (s : unitInterval) :
    (stableTorus F a b).val (0,s) = stableAxis F (1,b) s := by
  change stableDiagonalSource F (rawTorus F a b (0,s)) = _
  rw [rawTorus_zero_first]
  rfl

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup SSet
open scoped Topology unitInterval commutatorElement
universe u v
namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective StableCompletion
variable (F : Type u) [Field F]

/-- The actual target comparison is bijective in every positive degree at the original image. -/
theorem zeroToStageThreeQLoops_pi_bijective (n : ℕ) :
    Function.Bijective (piMap n (zeroToStageThreeQLoops F)
      (x := stableZeroMap F (stableBase F)) rfl) := by
  have hi := (homotopyGroupMap_bijective_iff_of_path
    (pathComponentInclusion (zeroPoint F)) (basepointPath F).symm (n + 1)).mp
      (homotopyGroupMap_pathComponent_bijective (N := Fin (n + 1)) (zeroPoint F))
  exact homotopyGroupMap_bijective_comp (pathComponentInclusion (zeroPoint F))
    (stageThreeQMap F) rfl rfl (n + 1) hi
      ((completionToOriginalQLoops_isWeakHomotopyEquivalence Fᵐᵒᵖ
        (stageObject F 3)).homotopy_bijective _ (n + 1))

/-- The homotopy fiber of the original stable loop map at its basepoint image. -/
abbrev OriginalLoopFiber :=
  HomotopyFiber (stableOriginalLoopMap F) (stableOriginalLoopMap F (stableBase F))

/-- The canonical basepoint in the original loop fiber. -/
def originalLoopFiberBase :=
  HomotopyFiber.basepoint (stableOriginalLoopMap F)
    (stableOriginalLoopMap F (stableBase F)) (stableBase F) rfl

/-- The fundamental group of the original loop fiber. -/
abbrev OriginalLoopFiberPiOne := HomotopyGroup.Pi 1 (OriginalLoopFiber F) (originalLoopFiberBase F)

/-- The original loop-fiber projection on fundamental groups. -/
def originalLoopFiberProjection : OriginalLoopFiberPiOne F →*
    HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj (StableGeneralLinear.Group F)))
      (stableBase F) :=
  piMap 0 (HomotopyFiber.projection (stableOriginalLoopMap F)
    (stableOriginalLoopMap F (stableBase F)))
      (HomotopyFiber.projection_basepoint _ _ _ rfl)

/-- This is the actual strict fiber map, with the original target postcomposition. -/
def originalLoopFiberMap :=
  HomotopyFiber.mapAt (ContinuousMap.id _) (zeroToStageThreeQLoops F)
    (stableOriginalLoopMap_square F) (stableZeroMap F (stableBase F))
      (stableOriginalLoopMap F (stableBase F)) rfl

theorem originalLoopFiberMap_basepoint :
    originalLoopFiberMap F (stableFiberBase F) = originalLoopFiberBase F :=
  HomotopyFiber.mapAt_basepoint (ContinuousMap.id _) (zeroToStageThreeQLoops F)
    (stableOriginalLoopMap_square F) (stableBase F) (stableZeroMap F (stableBase F))
      (stableBase F) (stableOriginalLoopMap F (stableBase F)) rfl rfl rfl rfl

/-- The original stable-fiber map on fundamental groups. -/
def originalLoopFiberPiOne : StableFiberPiOne F →* OriginalLoopFiberPiOne F :=
  piMap 0 (originalLoopFiberMap F) (originalLoopFiberMap_basepoint F)

theorem originalLoopFiberPiOne_bijective : Function.Bijective (originalLoopFiberPiOne F) :=
  HomotopyFiber.mapAt_piOne_bijective (stableZeroMap F) (stableOriginalLoopMap F)
    (zeroToStageThreeQLoops F) (stableOriginalLoopMap_square F) (stableBase F)
      (stableZeroMap F (stableBase F)) rfl (stableOriginalLoopMap F (stableBase F)) rfl rfl
        (zeroToStageThreeQLoops_pi_bijective F 0).injective
        (zeroToStageThreeQLoops_pi_bijective F 1)

theorem originalLoopFiberPiOne_projection (a : StableFiberPiOne F) :
    originalLoopFiberProjection F (originalLoopFiberPiOne F a) =
      stableFiberPiOneProjection F a := by
  have h := DFunLike.congr_fun (HomotopyFiber.projectionHom_mapAt_natural
    (ContinuousMap.id _) (zeroToStageThreeQLoops F) (stableOriginalLoopMap_square F)
      (stableBase F) (stableZeroMap F (stableBase F)) (stableBase F)
        (stableOriginalLoopMap F (stableBase F)) rfl rfl rfl rfl 0) a
  change originalLoopFiberProjection F (originalLoopFiberPiOne F a) =
    HomotopyGroup.map (ContinuousMap.id _) rfl (stableFiberPiOneProjection F a) at h
  simpa only [HomotopyGroup.map_id] using h

/-- Original connecting naturality under the actual target map. -/
theorem originalLoopFiberPiOne_connecting
    (a : HomotopyGroup.Pi 2 (ZeroComponent F) (stableZeroMap F (stableBase F))) :
    originalLoopFiberPiOne F (stableFiberConnecting F a) =
      HomotopyFiber.connectingHom (stableOriginalLoopMap F)
        (stableOriginalLoopMap F (stableBase F)) (stableBase F) rfl 0
          (piMap 1 (zeroToStageThreeQLoops F) rfl a) :=
  DFunLike.congr_fun (HomotopyFiber.connectingHom_mapAt_natural (ContinuousMap.id _)
    (zeroToStageThreeQLoops F) (stableOriginalLoopMap_square F)
      (stableBase F) (stableZeroMap F (stableBase F)) (stableBase F)
        (stableOriginalLoopMap F (stableBase F)) rfl rfl rfl rfl 0) a

/-- The comparison cap keeps the original stable basepoint path, the actual stage edge,
and the prescribed completion-to-Q cap, in that order. -/
def originalLoopBasePath : Path (stableOriginalLoopMap F (stableBase F))
    (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) :=
  (((basepointPath F).map (zeroToStageThreeQLoops F).continuous).trans
    ((zeroToStagePath F 3).map (stageThreeQMap F).continuous)).trans
      (completionToOriginalQLoopsBasepointPath Fᵐᵒᵖ (stageObject F 3))

/-- The original e₂ and T₂ (and every positive-degree analogue) are retained exactly. -/
theorem originalLoopBasePath_positiveComparison (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent F) (stableZeroMap F (stableBase F))) :
    (loopShiftMulEquiv n).symm
      (pathTransportMulEquiv (originalLoopBasePath F) n
        (piMap n (zeroToStageThreeQLoops F) rfl a)) =
      zeroCompletionPositiveKEquiv F n (pathTransportMulEquiv (basepointPath F) n a) := by
  change (loopShiftMulEquiv n).symm
    (pathTransport (originalLoopBasePath F) (n + 1)
      (HomotopyGroup.map (zeroToStageThreeQLoops F) rfl a)) = _
  rw [originalLoopBasePath, pathTransport_trans, pathTransport_trans]
  erw [pathTransport_naturality]
  erw [show HomotopyGroup.map (zeroToStageThreeQLoops F) rfl
      (pathTransport (basepointPath F) (n + 1) a) =
    HomotopyGroup.map (stageThreeQMap F) rfl
      (HomotopyGroup.map (pathComponentInclusion (zeroPoint F)) rfl
        (pathTransport (basepointPath F) (n + 1) a)) from
    HomotopyGroup.map_comp (pathComponentInclusion (zeroPoint F)) rfl (stageThreeQMap F) rfl _]
  erw [pathTransport_naturality]
  exact completionPositiveKEquiv_pathTransport Fᵐᵒᵖ (zeroToStagePath F 3) n _

/-- Any two actual paths between loop-space points induce the same homotopy-group transport.
This is a class-level fact, derived from original whole-loop component translation. -/
theorem loop_pathTransport_independent {X : Type v} [TopologicalSpace X] {x : X}
    {p q : Path x x} (c d : Path p q) (n : ℕ) (a : HomotopyGroup.Pi n (Path x x) p) :
    pathTransport c n a = pathTransport d n a := by
  obtain ⟨b, rfl⟩ := (loopComponentHomotopyEquiv p n).surjective a
  exact (loopComponentHomotopyEquiv_pathTransport c n b).trans
    (loopComponentHomotopyEquiv_pathTransport d n b).symm

/-- The cap supplied by the periodic geometry may replace the displayed comparison cap
only after passage to homotopy classes. The original e₂/T₂ are still on the right. -/
theorem anyLoopCap_positiveComparison
    (c : Path (stableOriginalLoopMap F (stableBase F))
      (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent F) (stableZeroMap F (stableBase F))) :
    (loopShiftMulEquiv n).symm
      (pathTransportMulEquiv c n (piMap n (zeroToStageThreeQLoops F) rfl a)) =
      zeroCompletionPositiveKEquiv F n (pathTransportMulEquiv (basepointPath F) n a) := by
  change (loopShiftMulEquiv n).symm
    (pathTransport c (n + 1) (piMap n (zeroToStageThreeQLoops F) rfl a)) = _
  rw [loop_pathTransport_independent c (originalLoopBasePath F)]
  exact originalLoopBasePath_positiveComparison F n a

/-- Undoing the original e₂/T₂ and then changing the actual target gives the
original connecting map with precisely the chosen geometric cap. -/
theorem originalLoopFiberPiOne_kTwo
    (c : Path (stableOriginalLoopMap F (stableBase F))
      (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)) (k : (exactStructure Fᵐᵒᵖ).K 2) :
    originalLoopFiberPiOne F (FGModuleCat.SymbolMarking.kTwoToFiber F k) =
      HomotopyFiber.connectingHom (stableOriginalLoopMap F)
        (stableOriginalLoopMap F (stableBase F)) (stableBase F) rfl 0
          ((pathTransportMulEquiv c 1).symm (loopShiftMulEquiv 1 k)) := by
  let z := (pathTransportMulEquiv (basepointPath F) 1).symm
    ((zeroCompletionPositiveKEquiv F 1).symm k)
  change originalLoopFiberPiOne F (stableFiberConnecting F z) = _
  rw [originalLoopFiberPiOne_connecting]
  apply congrArg (HomotopyFiber.connectingHom (stableOriginalLoopMap F)
    (stableOriginalLoopMap F (stableBase F)) (stableBase F) rfl 0)
  apply (pathTransportMulEquiv c 1).injective
  rw [MulEquiv.apply_symm_apply]
  apply (loopShiftMulEquiv 1).symm.injective
  rw [MulEquiv.symm_apply_apply, anyLoopCap_positiveComparison]
  dsimp only [z]
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- The two scalar-cube inversions are exposed before the connecting sweep is used. -/
theorem originalLoopScalarBoundary (a b : Fˣ)
    (c : Path (stableOriginalLoopMap F (stableBase F))
      (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)) :
    originalLoopFiberPiOne F
      (FGModuleCat.SymbolMarking.kTwoToFiber F (FGModuleCat.SymbolMarking.scalarClass F a b)) =
      (HomotopyFiber.connectingHom (stableOriginalLoopMap F)
        (stableOriginalLoopMap F (stableBase F)) (stableBase F) rfl 0
          ((pathTransportMulEquiv c 1).symm
            (Quotient.mk' (scalarLoopCube F a b))))⁻¹ := by
  rw [originalLoopFiberPiOne_kTwo F c]
  let d := HomotopyFiber.connectingHom (stableOriginalLoopMap F)
    (stableOriginalLoopMap F (stableBase F)) (stableBase F) rfl 0
  let e := (pathTransportMulEquiv c 1).symm
  let L := loopShiftMulEquiv (x := (exactStructure Fᵐᵒᵖ).kBasepoint) 1
  let k := FGModuleCat.SymbolMarking.scalarClass F a b
  have hβ : (Quotient.mk' (scalarLoopCube F a b) :
      HomotopyGroup.Pi 2 (Path (exactStructure Fᵐᵒᵖ).kBasepoint
        (exactStructure Fᵐᵒᵖ).kBasepoint) (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)) =
      (L k)⁻¹ := by
    apply L.symm.injective
    exact (scalarLoopCube_originalClass F a b).trans
      ((L.symm.map_inv (L k)).trans
        (congrArg Inv.inv (L.symm_apply_apply k))).symm
  change d (e (L k)) = (d (e (Quotient.mk' (scalarLoopCube F a b))))⁻¹
  have hi := congrArg (d.comp e.toMonoidHom) hβ
  change d (e (Quotient.mk' (scalarLoopCube F a b))) = d (e (L k)⁻¹) at hi
  rw [map_inv, map_inv] at hi
  simpa only [inv_inv] using (congrArg Inv.inv hi).symm

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup SSet
open scoped Topology unitInterval commutatorElement
universe u v
namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective StableCompletion
open HomotopyFiber
open HomotopyFiber.PeriodicConnecting

/-- Uncurry a genuine periodic path, retaining its exact two square coordinates. -/
def periodicSquarePathHomotopy {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (T : PeriodicSquare X)
    {y : Y} (β : GenLoop (Fin 2) Y y)
    (P : Path (periodicPost f T) (periodicOfCube β)) :
    (f.comp T.val).Homotopy (cubeSquare y β) where
  toFun z := (P z.1).val z.2
  continuous_toFun := by fun_prop
  map_zero_left z := by
    exact congrArg (fun q : PeriodicSquare Y => q.val z) P.source
  map_one_left z := by
    refine (congrArg (fun q : PeriodicSquare Y => q.val z) P.target).trans ?_
    apply congrArg β
    funext i
    fin_cases i <;> rfl

variable (F : Type u) [Field F]

/-- The homotopy comparing the stable torus with the original scalar cube. -/
def stableCubeHomotopy (a b : Fˣ) :=
  periodicSquarePathHomotopy (stableOriginalLoopMap F) (stableTorus F a b)
    (scalarLoopCube F a b) (stableToScalarCube F a b)

theorem stableCubeHomotopy_first_periodic (a b : Fˣ) (u s : unitInterval) :
    stableCubeHomotopy F a b (u,(0,s)) = stableCubeHomotopy F a b (u,(1,s)) :=
  (stableToScalarCube F a b u).property.1 s

theorem stableCubeHomotopy_second_periodic (a b : Fˣ) (u t : unitInterval) :
    stableCubeHomotopy F a b (u,(t,0)) = stableCubeHomotopy F a b (u,(t,1)) :=
  (stableToScalarCube F a b u).property.2 t

/-- The actual cap is the full, possibly nonstationary vertex track of the proved prism. -/
def geometricCap (a b : Fˣ) :=
  vertexTrackAt (stableOriginalLoopMap F) (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)
    (stableTorus F a b).val (scalarLoopCube F a b) (stableCubeHomotopy F a b)
      (stableBase F) (stableTorus_vertex F a b)

/-- The homotopy fiber over the constant Q-loop. -/
abbrev GeometricFiber (_a _b : Fˣ) :=
  HomotopyFiber (stableOriginalLoopMap F) (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)

/-- The fiber point determined by the geometric cap. -/
def geometricFiberBase (a b : Fˣ) : GeometricFiber F a b :=
  pointWithPath (stableOriginalLoopMap F) (stableBase F)
    (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) (geometricCap F a b)

/-- The fundamental group based at the geometric cap. -/
abbrev GeometricFiberPiOne (a b : Fˣ) :=
  HomotopyGroup.Pi 1 (GeometricFiber F a b) (geometricFiberBase F a b)

/-- The first marked axis loop at the geometric fiber point. -/
def firstGeometricLoop (a b : Fˣ) :
    Path (geometricFiberBase F a b) (geometricFiberBase F a b) :=
  firstAxisAt (stableOriginalLoopMap F) (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)
    (stableTorus F a b).val (scalarLoopCube F a b) (stableCubeHomotopy F a b)
      (stableBase F) (stableTorus_vertex F a b) (stableTorus F a b).property.1
        (stableCubeHomotopy_first_periodic F a b)

/-- The second marked axis loop at the geometric fiber point. -/
def secondGeometricLoop (a b : Fˣ) :
    Path (geometricFiberBase F a b) (geometricFiberBase F a b) :=
  secondAxisAt (stableOriginalLoopMap F) (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)
    (stableTorus F a b).val (scalarLoopCube F a b) (stableCubeHomotopy F a b)
      (stableBase F) (stableTorus_vertex F a b) (stableTorus F a b).property.2
        (stableCubeHomotopy_second_periodic F a b)

/-- The actual periodic sweep supplies the inverse commutator sign. -/
theorem geometricConnecting_commutator (a b : Fˣ) :
    connectingAtPath (stableOriginalLoopMap F)
      (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) (stableBase F) (geometricCap F a b)
        (Quotient.mk' (scalarLoopCube F a b)) =
      ⁅loopClass (firstGeometricLoop F a b), loopClass (secondGeometricLoop F a b)⁆⁻¹ :=
  connecting_eq_commutator_inv_at (stableOriginalLoopMap F)
    (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) (stableTorus F a b).val
      (scalarLoopCube F a b) (stableCubeHomotopy F a b) (stableBase F)
        (stableTorus_vertex F a b) (stableTorus F a b).property.1
          (stableTorus F a b).property.2 (stableCubeHomotopy_first_periodic F a b)
            (stableCubeHomotopy_second_periodic F a b)

/-- Actual strict target base change followed by actual endpoint change. -/
def geometricFiberPiOneEquiv (a b : Fˣ) : StableFiberPiOne F ≃* GeometricFiberPiOne F a b :=
  (MulEquiv.ofBijective (originalLoopFiberPiOne F) (originalLoopFiberPiOne_bijective F)).trans
    (endpointPiOneEquiv (stableOriginalLoopMap F) (stableBase F)
      (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) (geometricCap F a b))

/-- The geometric fiber projection on fundamental groups. -/
def geometricProjection (a b : Fˣ) : GeometricFiberPiOne F a b →*
    HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj (StableGeneralLinear.Group F)))
      (stableBase F) :=
  piMap 0 (projection (stableOriginalLoopMap F) (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)) rfl

theorem geometricFiberPiOneEquiv_projection (a b : Fˣ) (z : StableFiberPiOne F) :
    geometricProjection F a b (geometricFiberPiOneEquiv F a b z) =
      stableFiberPiOneProjection F z := by
  change piMap 0 (projection (stableOriginalLoopMap F)
    (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)) rfl
      (endpointPiOneEquiv (stableOriginalLoopMap F) (stableBase F)
        (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) (geometricCap F a b)
          (originalLoopFiberPiOne F z)) = _
  rw [endpointPiOneEquiv_projection]
  exact originalLoopFiberPiOne_projection F z

theorem stableAxis_class (g : Fˣ × Fˣ) :
    loopClass (stableAxis F g) =
      piMap 0 (stableDiagonalSource F) (stableDiagonalSource_point F) (sourcePiOne F g) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [loopClass_toFundamentalGroup]
  change FundamentalGroup.fromPath ⟦stableAxis F g⟧ =
    HomotopyGroup.pi1MulEquivFundamentalGroup
      (HomotopyGroup.map (stableDiagonalSource F) (stableDiagonalSource_point F)
        (sourcePiOne F g))
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  erw [MulEquiv.apply_symm_apply]
  rw [FundamentalGroup.mapOfEq_apply]
  rfl

theorem firstGeometric_projection (a b : Fˣ) :
    geometricProjection F a b (loopClass (firstGeometricLoop F a b)) =
      stableFiberPiOneProjection F (steinbergToStableFiber F (StableSteinberg.h a)) := by
  change piMap 0 (projection (stableOriginalLoopMap F)
    (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)) rfl
      (loopClass (firstGeometricLoop F a b)) = _
  rw [loopClass_map]
  have he : (firstGeometricLoop F a b).map
      (projection (stableOriginalLoopMap F)
        (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)).continuous =
        stableAxis F (a,1) := by
    apply Path.ext
    funext t
    exact stableTorus_first F a b t
  rw [he, stableAxis_class, stableDiagonalSource_first_class]

theorem secondGeometric_projection (a b : Fˣ) :
    geometricProjection F a b (loopClass (secondGeometricLoop F a b)) =
      stableFiberPiOneProjection F (steinbergToStableFiber F (StableSteinberg.h02 b)) := by
  change piMap 0 (projection (stableOriginalLoopMap F)
    (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)) rfl
      (loopClass (secondGeometricLoop F a b)) = _
  rw [loopClass_map]
  have he : (secondGeometricLoop F a b).map
      (projection (stableOriginalLoopMap F)
        (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)).continuous =
        stableAxis F (1,b) := by
    apply Path.ext
    funext t
    exact stableTorus_second F a b t
  rw [he, stableAxis_class, stableDiagonalSource_second_class]

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup SSet
open scoped Topology commutatorElement
universe u
namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective StableCompletion
open HomotopyFiber.PeriodicConnecting
variable (F : Type u) [Field F]

/-- Pull the first actual prism axis back through the actual target and endpoint comparisons. -/
def firstGeometricLift (a b : Fˣ) : StableFiberPiOne F :=
  (geometricFiberPiOneEquiv F a b).symm (loopClass (firstGeometricLoop F a b))

/-- Pull the second actual prism axis back through those same comparisons. -/
def secondGeometricLift (a b : Fˣ) : StableFiberPiOne F :=
  (geometricFiberPiOneEquiv F a b).symm (loopClass (secondGeometricLoop F a b))

theorem firstGeometricLift_projection (a b : Fˣ) :
    stableFiberPiOneProjection F (firstGeometricLift F a b) =
      stableFiberPiOneProjection F (steinbergToStableFiber F (StableSteinberg.h a)) := by
  rw [← geometricFiberPiOneEquiv_projection F a b]
  change geometricProjection F a b ((geometricFiberPiOneEquiv F a b)
    ((geometricFiberPiOneEquiv F a b).symm (loopClass (firstGeometricLoop F a b)))) = _
  rw [MulEquiv.apply_symm_apply]
  exact firstGeometric_projection F a b

theorem secondGeometricLift_projection (a b : Fˣ) :
    stableFiberPiOneProjection F (secondGeometricLift F a b) =
      stableFiberPiOneProjection F (steinbergToStableFiber F (StableSteinberg.h02 b)) := by
  rw [← geometricFiberPiOneEquiv_projection F a b]
  change geometricProjection F a b ((geometricFiberPiOneEquiv F a b)
    ((geometricFiberPiOneEquiv F a b).symm (loopClass (secondGeometricLoop F a b)))) = _
  rw [MulEquiv.apply_symm_apply]
  exact secondGeometric_projection F a b

theorem elementaryProjection_congr {A B : StableFiberPiOne F}
    (h : stableFiberPiOneProjection F A = stableFiberPiOneProjection F B) :
    stableFiberToElementary F A = stableFiberToElementary F B := by
  apply Subtype.ext
  exact congrArg (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).symm h

theorem firstGeometricLift_elementary (a b : Fˣ) :
    stableFiberToElementary F (firstGeometricLift F a b) =
      StableSteinberg.toElementary F (StableSteinberg.h a) :=
  (elementaryProjection_congr F (firstGeometricLift_projection F a b)).trans
    (DFunLike.congr_fun (steinbergToStableFiber_over F) (StableSteinberg.h a))

theorem secondGeometricLift_elementary (a b : Fˣ) :
    stableFiberToElementary F (secondGeometricLift F a b) =
      StableSteinberg.toElementary F (StableSteinberg.h02 b) :=
  (elementaryProjection_congr F (secondGeometricLift_projection F a b)).trans
    (DFunLike.congr_fun (steinbergToStableFiber_over F) (StableSteinberg.h02 b))

/-- The original scalar boundary is the positive ordered commutator of the actual prism lifts. -/
theorem scalarClass_boundary_commutator (a b : Fˣ) :
    kTwoToFiber F (scalarClass F a b) =
      ⁅firstGeometricLift F a b, secondGeometricLift F a b⁆ := by
  apply (geometricFiberPiOneEquiv F a b).injective
  rw [map_commutatorElement]
  have hA : geometricFiberPiOneEquiv F a b (firstGeometricLift F a b) =
      loopClass (firstGeometricLoop F a b) := (geometricFiberPiOneEquiv F a b).apply_symm_apply _
  have hB : geometricFiberPiOneEquiv F a b (secondGeometricLift F a b) =
      loopClass (secondGeometricLoop F a b) := (geometricFiberPiOneEquiv F a b).apply_symm_apply _
  rw [hA, hB]
  change endpointPiOneEquiv (stableOriginalLoopMap F) (stableBase F)
    (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) (geometricCap F a b)
      (originalLoopFiberPiOne F (kTwoToFiber F (scalarClass F a b))) = _
  rw [originalLoopScalarBoundary F a b (geometricCap F a b), map_inv,
    endpointPiOneEquiv_connecting_inverse, geometricConnecting_commutator, inv_inv]

/-- The actual ordered Steinberg defect has the original positive scalar product marking.
All maps, the forward opposite unit, the positive rank-one input, and both signs
are the originals. -/
theorem steinbergKernel_original_scalar_marking (a b : Fˣ) :
    steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b) =
      CategoryTheory.ExactCategory.ScalarUnit.finiteProjectiveKOneAction Fᵐᵒᵖ
        (opUnit F a) (positiveRankOneKOne F b) :=
  (arbitrary_lifts_comparison_iff F a b (firstGeometricLift F a b) (secondGeometricLift F a b)
    (firstGeometricLift_elementary F a b) (secondGeometricLift_elementary F a b)).mpr
      (scalarClass_boundary_commutator F a b)

end FGModuleCat.SymbolMarking

end

section
open CategoryTheory CategoryTheory.Linear CategoryTheory.ExactCategory Topology HomotopyGroup
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace FGModuleCat.SymbolMarking
open ModuleCat.FiniteProjective ModuleCat.FiniteProjective.StableCompletion
variable (F : Type u) [Field F]

/-- The original projective inclusion retains the actual scalar component. -/
theorem projectiveInclusion_scalar_component (a : Fˣ)
    (P : ModuleCat.FiniteProjective.Category.{u, u} Fᵐᵒᵖ) :
    (toFiniteModuleExact Fᵐᵒᵖ).toFunctor.map
      (((scalarNatAut Fᵐᵒᵖ (ModuleCat.FiniteProjective.Category.{u, u} Fᵐᵒᵖ)
        (opUnit F a)).asIso).hom.app P) =
      ((scalarNatAut Fᵐᵒᵖ (FGModuleCat.{u} Fᵐᵒᵖ) (opUnit F a)).asIso).hom.app
        ((toFiniteModuleExact Fᵐᵒᵖ).toFunctor.obj P) := by
  apply (ModuleCat.isFG Fᵐᵒᵖ).ι.map_injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The original opposite-ring restriction retains the forward scalar coefficient. -/
theorem oppositeRestriction_scalar_component (a : Fˣ) (P : FGModuleCat.{u} Fᵐᵒᵖ) :
    (FGModuleCat.finiteModuleRingExact (RingEquiv.toOpposite F)).toFunctor.map
      (((scalarNatAut Fᵐᵒᵖ (FGModuleCat.{u} Fᵐᵒᵖ) (opUnit F a)).asIso).hom.app P) =
      ((scalarNatAut F (FGModuleCat.{u} F) a).asIso).hom.app
        ((FGModuleCat.finiteModuleRingExact (RingEquiv.toOpposite F)).toFunctor.obj P) := by
  apply (ModuleCat.isFG F).ι.map_injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The original positive matrix input is the determinant's actual inverse class
in the literal upper finite-module model. -/
theorem positiveRankOne_upper (b : Fˣ) :
    FGModuleCat.rightProjectiveUpperModuleKEquiv F 1 (positiveRankOneKOne F b) =
      FieldSymbols.positiveUnitKOne F b := by
  apply (FGModuleCat.moduleDetEquiv F).injective
  change FGModuleCat.moduleDetEquiv F
    (FGModuleCat.rightProjectiveUpperModuleKEquiv F 1 (positiveRankOneKOne F b)) =
      FGModuleCat.moduleDetEquiv F ((FGModuleCat.moduleDetEquiv F).symm b)
  rw [MulEquiv.apply_symm_apply, positiveRankOneKOne, FGModuleCat.moduleDetEquiv_matrix,
    Matrix.GeneralLinearGroup.det_scalar]
  simp

/-- The original upper comparison preserves the actual scalar identity-track
operation. Its proof follows inclusion, opposite restriction and the inverse
common-ambient SmallModel map, without creating a replacement comparison. -/
theorem rightProjectiveUpper_scalar_action (a : Fˣ)
    (x : (exactStructure Fᵐᵒᵖ).K 1) :
    FGModuleCat.rightProjectiveUpperModuleKEquiv F 2
      (ScalarUnit.finiteProjectiveKOneAction Fᵐᵒᵖ (opUnit F a) x) =
      ScalarUnit.upperFiniteModuleKOneAction F a
        (FGModuleCat.rightProjectiveUpperModuleKEquiv F 1 x) := by
  let E := abelianExactStructure (FGModuleCat.{u} F)
  let I := toFiniteModuleExact Fᵐᵒᵖ
  let O := FGModuleCat.finiteModuleRingExact (RingEquiv.toOpposite F)
  let J := E.smallModelToOriginal.{u+1}
  let α := (scalarNatAut Fᵐᵒᵖ (ModuleCat.FiniteProjective.Category.{u, u} Fᵐᵒᵖ) (opUnit F a)).asIso
  let β := (scalarNatAut Fᵐᵒᵖ (FGModuleCat.{u} Fᵐᵒᵖ) (opUnit F a)).asIso
  let γ := (scalarNatAut F (FGModuleCat.{u} F) a).asIso
  let δ := (smallModelScalarNatAut.{u, u+1, u, u+1} F (FGModuleCat.{u} F) a).asIso
  have hJ (P : SmallModel.{u+1} (FGModuleCat.{u} F)) :
      J.toFunctor.map (δ.hom.app P) = γ.hom.app (J.toFunctor.obj P) :=
    smallModelScalarNatAut_map_hom F (FGModuleCat.{u} F) a P
  apply (J.commonAmbientKEquiv 2).injective
  change J.commonAmbientKMap 2
    (FGModuleCat.rightProjectiveUpperModuleKEquiv F 2
      (ScalarUnit.finiteProjectiveKOneAction Fᵐᵒᵖ (opUnit F a) x)) =
      J.commonAmbientKMap 2 (IdentityAutomorphism.kOneAction.{u + 1, u + 1} E.smallModel.{u + 1} δ
        (FGModuleCat.rightProjectiveUpperModuleKEquiv F 1 x))
  rw [FGModuleCat.rightProjectiveUpperModuleKEquiv_toOriginal]
  change O.KMap 2 (I.KMap 2 (IdentityAutomorphism.kOneAction (exactStructure Fᵐᵒᵖ) α x)) = _
  rw [IdentityAutomorphism.kOneAction_natural.{u + 1, u} I α β
      (projectiveInclusion_scalar_component F a),
    IdentityAutomorphism.kOneAction_natural.{u + 1, u} O β γ
      (oppositeRestriction_scalar_component F a),
    IdentityAutomorphism.kOneAction_commonAmbient_natural.{u + 1, u} J δ γ hJ]
  rw [FGModuleCat.rightProjectiveUpperModuleKEquiv_toOriginal]

/-- The genuine scalar-action square identifies the original ordered product. -/
theorem rightProjectiveUpper_scalarClass (a b : Fˣ) :
    FGModuleCat.rightProjectiveUpperModuleKEquiv F 2 (scalarClass F a b) =
      FieldSymbols.unitProduct F a b := by
  rw [scalarClass, rightProjectiveUpper_scalar_action, positiveRankOne_upper]
  rfl

/-- The native ordered Milnor pair has the original positive right-projective scalar class. -/
theorem milnorToRightProjectiveKTwo_positive_pair (a b : Fˣ) :
    MilnorKTheory.toRightProjectiveKTwo F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (scalarClass F a b) := by
  rw [MilnorKTheory.toRightProjectiveKTwo_pair]
  exact congrArg Additive.ofMul (steinbergKernel_original_scalar_marking F a b)

/-- The actual upper finite-module ordered symbol has its original positive unit product. -/
theorem milnorToUpperModuleKTwo_positive_pair (a b : Fˣ) :
    MilnorKTheory.toUpperModuleKTwo F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (FieldSymbols.unitProduct F a b) := by
  rw [MilnorKTheory.toUpperModuleKTwo_pair, steinbergKernel_original_scalar_marking]
  exact congrArg Additive.ofMul (rightProjectiveUpper_scalarClass F a b)

end FGModuleCat.SymbolMarking

namespace MilnorKTheory
/-- An ordered Milnor symbol maps to the original scalar unit product over every field. -/
theorem toUpperModuleKTwo_pair_eq_unitProduct (F : Type u) [Field F] (a b : Fˣ) :
    toUpperModuleKTwo F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct F a b) :=
  FGModuleCat.SymbolMarking.milnorToUpperModuleKTwo_positive_pair F a b
end MilnorKTheory
end

end

namespace MilnorKTheory

attribute [colib_tag "COL-0262",
  colib_ref "quillen"
    "Quillen/KTheory/Field/PositiveSymbolMarking.lean, milnorToUpperModuleKTwo_pair_eq_unitProduct"
    "adaptation" "Every field; ordered symbol and original scalar identity-action unit product"]
  toUpperModuleKTwo_pair_eq_unitProduct

end MilnorKTheory
