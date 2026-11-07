/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.Quillen.Field.SteinbergFiberComparison
public import Colib.GroupTheory.Steinberg.Symbols
public import Colib.RingTheory.KTheory.MilnorK.Steinberg
public import Colib.RingTheory.KTheory.Quillen.LowDegreeScalarAction.ScalarUnit
public import Colib.LinearAlgebra.Matrix.RightAutomorphismsLeft
public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateTransposition
public import Colib.KTheory.Quillen.LowDegreeScalarAction.BiproductLoopFamilies
public import Colib.CategoryTheory.GroupCompletion.StableFreeDiagram
public import Colib.RingTheory.KTheory.Quillen.Field.StableMatrixMarking
public import Colib.Topology.Homotopy.HomotopyGroup.PeriodicLoopFamilies
public import Colib.Topology.ClassifyingSpace.FunctorChain

/-!
# The original right-projective scalar class and its rank-three torus source

The original right-projective scalar class and its rank-three torus source.

All comparisons retain the original maps and require only the stated hypotheses.
-/
/-! Adapted from `Quillen/KTheory/Field/SymbolMarking/RankThree.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. All matrices, original core rows,
zero-first paths, coordinate orders and signs are retained. Optional projective
determinant calibration is omitted; the final upper marking uses moduleDetEquiv_matrix. -/
@[expose] public section
noncomputable section

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped commutatorElement
open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup

universe u v w

namespace FGModuleCat.SymbolMarking

variable (F : Type u) [Field F]

/-- Literal opposition of a unit. There is no inversion of its coefficient. -/
def opUnit (a : Fˣ) : Fᵐᵒᵖˣ := Units.opEquiv.symm (MulOpposite.op a)

@[simp] theorem opUnit_val (a : Fˣ) :
    ((opUnit F a : Fᵐᵒᵖˣ) : Fᵐᵒᵖ) = MulOpposite.op (a : F) := rfl

/-- The transported scalar acts by the same matrix coefficient, with no inverse. -/
theorem right_scalar_matrix_apply (n : ℕ) (a : Fˣ)
    (x : Fin n → Fᵐᵒᵖ) (i : Fin n) :
    (Matrix.RightModule.moduleAutEquiv F n (Matrix.GeneralLinearGroup.scalar (Fin n)
      a)).asIso.hom x i =
      (opUnit F a : Fᵐᵒᵖ) • x i := by
  rw [Matrix.RightModule.moduleAutEquiv_hom_apply]
  change MulOpposite.op ((Matrix.diagonal (fun _ : Fin n => (a : F))).mulVec
      (fun j => MulOpposite.unop (x j)) i) = MulOpposite.op (a : F) * x i
  rw [Matrix.mulVec_diagonal]
  apply MulOpposite.unop_injective
  exact mul_comm _ _

/-- The actual reversed-basis matrix action retains that scalar coefficient. -/
theorem left_right_scalar_matrix_apply (n : ℕ) (a : Fˣ)
    (x : Fin n → Fᵐᵒᵖ) (i : Fin n) :
    (Matrix.RightModule.leftModuleAutEquiv F n
      (Matrix.GeneralLinearGroup.scalar (Fin n) a)).asIso.hom x i =
      (opUnit F a : Fᵐᵒᵖ) • x i := by
  rw [Matrix.RightModule.leftModuleAutEquiv_apply, right_scalar_matrix_apply]
  simp

open ModuleCat.FiniteProjective StableCompletion

/-- The original positive rank-one stable matrix class. -/
def positiveRankOneKOne (b : Fˣ) : (exactStructure Fᵐᵒᵖ).K 1 :=
  zeroCompletionPositiveKEquiv F 0
    (stableGroupPiOneMap F
      (StableGeneralLinear.of F 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) b)))

/-- The exact scalar side of the assignment, in the original right-module group. -/
def scalarClass (a b : Fˣ) : (exactStructure Fᵐᵒᵖ).K 2 :=
  CategoryTheory.ExactCategory.ScalarUnit.finiteProjectiveKOneAction Fᵐᵒᵖ
    (opUnit F a) (positiveRankOneKOne F b)

/-- Undo only the original comparisons, then apply the original connecting map. -/
def kTwoToFiber : (exactStructure Fᵐᵒᵖ).K 2 →* StableFiberPiOne F :=
  (stableFiberConnecting F).comp
    (((pathTransportMulEquiv (basepointPath F) 1).symm.toMonoidHom).comp
      (zeroCompletionPositiveKEquiv F 1).symm.toMonoidHom)

theorem kTwoToFiber_injective : Function.Injective (kTwoToFiber F) := by
  intro a b h
  apply (zeroCompletionPositiveKEquiv F 1).symm.injective
  apply (pathTransportMulEquiv (basepointPath F) 1).symm.injective
  exact stableFiberConnecting_injective F h

theorem kTwoToFiber_kernel (z : (StableSteinberg.toElementary F).ker) :
    kTwoToFiber F (steinbergKernelToRightProjectiveKTwo F z) =
      steinbergToStableFiber F z := by
  change stableFiberConnecting F ((pathTransportMulEquiv (basepointPath F) 1).symm
    ((zeroCompletionPositiveKEquiv F 1).symm
      (steinbergKernelToRightProjectiveKTwo F z))) = _
  rw [steinbergKernelToRightProjectiveKTwo_apply, MulEquiv.symm_apply_apply]
  exact connecting_steinbergKernelToCompletionPiTwo F z

theorem kTwoToFiber_torus (a b : Fˣ) :
    kTwoToFiber F
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) =
      ⁅steinbergToStableFiber F (StableSteinberg.h a),
        steinbergToStableFiber F (StableSteinberg.h02 b)⁆ := by
  rw [kTwoToFiber_kernel, ← map_commutatorElement,
    StableSteinberg.commutator_h_h02]
  rfl

/-- A necessary-and-sufficient native boundary equation, with all signs explicit. -/
theorem positive_comparison_iff (a b : Fˣ) :
    steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b) =
        scalarClass F a b ↔
      kTwoToFiber F (scalarClass F a b) =
        ⁅steinbergToStableFiber F (StableSteinberg.h a),
          steinbergToStableFiber F (StableSteinberg.h02 b)⁆ := by
  constructor
  · intro h
    rw [← h, kTwoToFiber_torus]
  · intro h
    apply kTwoToFiber_injective F
    exact (kTwoToFiber_torus F a b).trans h.symm

section CentralLift

variable {A : Type v} {B : Type w} [_root_.Group A] [_root_.Group B]
variable (p : A →* B) (hc : p.ker ≤ Subgroup.center A)
include hc

theorem commutator_congr_left {a a' b : A} (ha : p a = p a') :
    ⁅a, b⁆ = ⁅a', b⁆ := by
  have hz : a * a'⁻¹ ∈ Subgroup.center A := hc (by simp [MonoidHom.mem_ker, ha])
  have hzb : Commute (a * a'⁻¹) b := (Subgroup.mem_center_iff.mp hz b).symm
  have hzc : Commute (a * a'⁻¹) ⁅a', b⁆ :=
    (Subgroup.mem_center_iff.mp hz ⁅a', b⁆).symm
  calc
    ⁅a, b⁆ = ⁅(a * a'⁻¹) * a', b⁆ := by simp
    _ = ⁅a', b⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hzb.commutator_eq,
        mul_one, hzc.eq, mul_inv_cancel_right]

theorem commutator_congr {a a' b b' : A}
    (ha : p a = p a') (hb : p b = p b') : ⁅a, b⁆ = ⁅a', b'⁆ := by
  rw [commutator_congr_left p hc ha]
  have h := congrArg Inv.inv (commutator_congr_left p hc (b := a') hb)
  simpa using h

end CentralLift

/-- Reversed chronological multiplication turns the oriented torus perimeter into
the inverse central commutator. -/
theorem chronological_perimeter {A : Type v} [_root_.Group A] (a b : A)
    (hc : ⁅a, b⁆ ∈ Subgroup.center A) :
    b⁻¹ * a⁻¹ * b * a = ⁅a, b⁆⁻¹ := by
  have h : Commute ⁅a, b⁆ (a * b) :=
    (Subgroup.mem_center_iff.mp hc (a * b)).symm
  calc
    _ = (a * b)⁻¹ * ⁅a, b⁆⁻¹ * (a * b) := by
      simp [commutatorElement_def, mul_assoc]
    _ = ⁅a, b⁆⁻¹ := by
      rw [h.inv_left.inv_right.symm.eq]
      simp [mul_assoc]

section CubeCycle

variable {X : Type v} [TopologicalSpace X] {x : X}

/-- Reorder (scalar, matrix, Q) to (Q, scalar, matrix) by exactly two transpositions. -/
def qFirstCycle (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  transposeGenLoop 0 2 (by decide)
    (transposeGenLoop 0 1 (by decide) p)

theorem qFirstCycle_class (p : GenLoop (Fin 3) X x) :
    (⟦qFirstCycle p⟧ : HomotopyGroup.Pi 3 X x) = ⟦p⟧ := by
  change (Quotient.mk' (transposeGenLoop (0 : Fin 3) 2 (by decide)
    (transposeGenLoop 0 1 (by decide) p)) : HomotopyGroup (Fin 3) X x) = Quotient.mk' p
  rw [transposeGenLoop_class, transposeGenLoop_class, inv_inv]

end CubeCycle

/-- Any geometrically constructed torus lifts suffice; their particular caps do not matter. -/
theorem arbitrary_lifts_comparison_iff (a b : Fˣ) (A B : StableFiberPiOne F)
    (hA : stableFiberToElementary F A = StableSteinberg.toElementary F (StableSteinberg.h a))
    (hB : stableFiberToElementary F B = StableSteinberg.toElementary F (StableSteinberg.h02 b)) :
    steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b) =
        scalarClass F a b ↔ kTwoToFiber F (scalarClass F a b) = ⁅A, B⁆ := by
  have hlift (z : StableSteinberg.Group F) :
      stableFiberToElementary F (steinbergToStableFiber F z) =
        StableSteinberg.toElementary F z :=
    DFunLike.congr_fun (steinbergToStableFiber_over F) z
  have hc : ⁅A, B⁆ =
      ⁅steinbergToStableFiber F (StableSteinberg.h a),
        steinbergToStableFiber F (StableSteinberg.h02 b)⁆ :=
    commutator_congr (stableFiberToElementary F) (ker_stableFiberToElementary_le_center F)
      (hA.trans (hlift _).symm) (hB.trans (hlift _).symm)
  rw [hc]
  exact positive_comparison_iff F a b

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Topology HomotopyGroup
open CategoryTheory CategoryTheory.Limits
open scoped Matrix

universe u

namespace FGModuleCat.SymbolMarking.Diagonal
open ModuleCat.FiniteProjective Matrix.RightModule
variable (F : Type u) [Field F]
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  preservesBinaryBiproducts_of_preservesBiproducts

/-- Diagonal matrices with their actual inverse entries. -/
def diagonalUnit (n : ℕ) (d : Fin n → Fˣ) : Matrix.GeneralLinearGroup (Fin n) F where
  val := Matrix.diagonal fun i => (d i : F)
  inv := Matrix.diagonal fun i => ((d i)⁻¹ : Fˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

theorem diagonalUnit_apply (n : ℕ) (d : Fin n → Fˣ)
    (x : Fin n → Fᵐᵒᵖ) (i : Fin n) :
    (leftModuleAutEquiv F n (diagonalUnit F n d)).asIso.hom x i =
      MulOpposite.op ((d i.rev : F) * MulOpposite.unop (x i)) := by
  rw [leftModuleAutEquiv_apply, moduleAutEquiv_hom_apply]
  change MulOpposite.op (((Matrix.diagonal fun i => (d i : F)) *ᵥ
    fun j => MulOpposite.unop (x j.rev)) i.rev) = _
  rw [Matrix.mulVec_diagonal, Fin.rev_rev]

theorem diagonalUnit_prepend_zero (n : ℕ) (d : Fin n → Fˣ) (a : Fˣ)
    (x : Fin (n + 1) → Fᵐᵒᵖ) :
    (leftModuleAutEquiv F (n + 1) (diagonalUnit F (n + 1) (Fin.snoc d a))).asIso.hom x 0 =
      (leftModuleAutEquiv F 1 (diagonalUnit F 1 (fun _ => a))).asIso.hom (fun _ => x 0) 0 := by
  rw [diagonalUnit_apply, diagonalUnit_apply]
  simp only [Fin.rev_zero, Fin.snoc_last]

theorem diagonalUnit_prepend_succ (n : ℕ) (d : Fin n → Fˣ) (a : Fˣ)
    (x : Fin (n + 1) → Fᵐᵒᵖ) (i : Fin n) :
    (leftModuleAutEquiv F (n + 1) (diagonalUnit F (n + 1) (Fin.snoc d a))).asIso.hom x i.succ =
      (leftModuleAutEquiv F n (diagonalUnit F n d)).asIso.hom (fun j => x j.succ) i := by
  rw [diagonalUnit_apply, diagonalUnit_apply]
  rw [Fin.rev_succ, Fin.snoc_castSucc]

/-- The exact module-level prepend isomorphism intertwines both varying diagonal blocks. -/
theorem diagonalUnit_module_prepend (n : ℕ) (d : Fin n → Fˣ) (a : Fˣ) :
    (leftModuleAutEquiv F (n + 1) (diagonalUnit F (n + 1) (Fin.snoc d a))).asIso.hom ≫
        (prependIso F n).inv =
      (prependIso F n).inv ≫ biprod.map
        (leftModuleAutEquiv F 1 (diagonalUnit F 1 (fun _ => a))).asIso.hom
        (leftModuleAutEquiv F n (diagonalUnit F n d)).asIso.hom := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, prependIso, Iso.trans_inv,
      ModuleCat.biprodIsoProd_inv_comp_fst]
    rw [← Category.assoc ((ModuleCat.biprodIsoProd (freeModule F 1) (freeModule F n)).inv),
      ModuleCat.biprodIsoProd_inv_comp_fst]
    ext x
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact diagonalUnit_prepend_zero F n d a x
  · simp only [Category.assoc, biprod.map_snd, prependIso, Iso.trans_inv,
      ModuleCat.biprodIsoProd_inv_comp_snd]
    rw [← Category.assoc ((ModuleCat.biprodIsoProd (freeModule F 1) (freeModule F n)).inv),
      ModuleCat.biprodIsoProd_inv_comp_snd]
    ext x
    funext i
    exact diagonalUnit_prepend_succ F n d a x i

private theorem inclusion_biprod_map (A B : ModuleCat.FiniteProjective.Category.{u, u} Fᵐᵒᵖ)
    (a : A ⟶ A) (b : B ⟶ B) :
    (property Fᵐᵒᵖ).ι.map (biprod.map a b) ≫
        ((property Fᵐᵒᵖ).ι.mapBiprod A B).hom =
      ((property Fᵐᵒᵖ).ι.mapBiprod A B).hom ≫
        biprod.map ((property Fᵐᵒᵖ).ι.map a) ((property Fᵐᵒᵖ).ι.map b) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Functor.mapBiprod_hom,
      biprod.lift_fst, biprod.lift_fst_assoc]
    exact congrArg (fun k : A ⊞ B ⟶ A => k.hom) (biprod.map_fst a b)
  · simp only [Category.assoc, biprod.map_snd, Functor.mapBiprod_hom,
      biprod.lift_snd, biprod.lift_snd_assoc]
    exact congrArg (fun k : A ⊞ B ⟶ B => k.hom) (biprod.map_snd a b)

/-- The original projective free-successor comparison retains the two actual diagonal actions. -/
theorem diagonalUnit_free_prepend (n : ℕ) (d : Fin n → Fˣ) (a : Fˣ) :
    (leftFreeAutEquiv F (n + 1) (diagonalUnit F (n + 1) (Fin.snoc d a))).asIso.hom ≫
        (freeSuccIso (R := Fᵐᵒᵖ) n).inv =
      (freeSuccIso (R := Fᵐᵒᵖ) n).inv ≫ biprod.map
        (leftFreeAutEquiv F 1 (diagonalUnit F 1 (fun _ => a))).asIso.hom
        (leftFreeAutEquiv F n (diagonalUnit F n d)).asIso.hom := by
  let I := (property Fᵐᵒᵖ).ι
  apply I.map_injective
  simp only [Functor.map_comp]
  apply (cancel_mono (I.mapBiprod (free (R := Fᵐᵒᵖ) 1) (free n)).hom).1
  rw [show I.map (freeSuccIso (R := Fᵐᵒᵖ) n).inv =
      (I.mapBiprod (free 1) (free n) ≪≫ prependIso F n).inv from
    congrArg Iso.inv (freeSuccIso_map F n)]
  simp only [Iso.trans_inv, Category.assoc]
  rw [inclusion_biprod_map F]
  dsimp only [I]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change I.map (leftFreeAutEquiv F (n + 1) _).asIso.hom ≫ (prependIso F n).inv =
    (prependIso F n).inv ≫ biprod.map
      (I.map (leftFreeAutEquiv F 1 _).asIso.hom) (I.map (leftFreeAutEquiv F n _).asIso.hom)
  rw [show I.map (leftFreeAutEquiv F (n + 1) _).asIso.hom =
      (leftModuleAutEquiv F (n + 1) (diagonalUnit F (n + 1) (Fin.snoc d a))).asIso.hom from
      congrArg Iso.hom (leftFreeAutEquiv_map F (n + 1) _),
    show I.map (leftFreeAutEquiv F 1 _).asIso.hom =
      (leftModuleAutEquiv F 1 (diagonalUnit F 1 (fun _ => a))).asIso.hom from
      congrArg Iso.hom (leftFreeAutEquiv_map F 1 _),
    show I.map (leftFreeAutEquiv F n _).asIso.hom =
      (leftModuleAutEquiv F n (diagonalUnit F n d)).asIso.hom from
      congrArg Iso.hom (leftFreeAutEquiv_map F n _)]
  exact diagonalUnit_module_prepend F n d a

/-- The same original isomorphism in the forward naturality direction. -/
theorem diagonalUnit_free_prepend_natural (n : ℕ) (d : Fin n → Fˣ) (a : Fˣ) :
    biprod.map (leftFreeAutEquiv F 1 (diagonalUnit F 1 (fun _ => a))).asIso.hom
        (leftFreeAutEquiv F n (diagonalUnit F n d)).asIso.hom ≫
        (freeSuccIso (R := Fᵐᵒᵖ) n).hom =
      (freeSuccIso (R := Fᵐᵒᵖ) n).hom ≫
        (leftFreeAutEquiv F (n + 1) (diagonalUnit F (n + 1) (Fin.snoc d a))).asIso.hom := by
  apply (cancel_epi (freeSuccIso (R := Fᵐᵒᵖ) n).inv).mp
  rw [← Category.assoc, ← diagonalUnit_free_prepend]
  simp [Category.assoc]

end FGModuleCat.SymbolMarking.Diagonal

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Topology HomotopyGroup
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped Topology ZeroObject

universe u

namespace FGModuleCat.SymbolMarking
open ModuleCat.FiniteProjective
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies

variable (F : Type u) [Field F]
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- One common groupoid for both torus parameters, before geometric realization. -/
abbrev TorusSource := SingleObj (Fˣ × Fˣ)

/-- The product character of the two unit coordinates. -/
def mixedCharacter : (Fˣ × Fˣ) →* Fˣ :=
  (MonoidHom.fst Fˣ Fˣ) * (MonoidHom.snd Fˣ Fˣ)

/-- The inverse of the first unit-coordinate character. -/
def firstInverseCharacter : (Fˣ × Fˣ) →* Fˣ := (MonoidHom.fst Fˣ Fˣ)⁻¹
/-- The inverse of the second unit-coordinate character. -/
def secondInverseCharacter : (Fˣ × Fˣ) →* Fˣ := (MonoidHom.snd Fˣ Fˣ)⁻¹

/-- Actual scalar matrices act on the original projective rank-one module. -/
def scalarRow (χ : (Fˣ × Fˣ) →* Fˣ) : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ :=
  ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp χ).toFunctor ⋙ StableFree.freeFunctor F 1

/-- The rank-one row carrying the product character. -/
def row0 : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ := scalarRow F (mixedCharacter F)
/-- The rank-one row carrying the inverse first character. -/
def row1 : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ := scalarRow F (firstInverseCharacter F)
/-- The rank-one row carrying the inverse second character. -/
def row2 : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ := scalarRow F (secondInverseCharacter F)

/-- The actual left-sum order reverses the original matrix basis order. -/
def rankThreeRow : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ :=
  biprodCore (row2 F) (biprodCore (row1 F) (row0 F))

@[simp] theorem scalarRow_obj (χ : (Fˣ × Fˣ) →* Fˣ) (d : TorusSource F) :
    (scalarRow F χ).obj d = freeIso Fᵐᵒᵖ 1 := rfl

/-- The two source generators act on the three summands by precisely the intended pairs. -/
theorem character_pairs (a b : Fˣ) :
    (mixedCharacter F (a, 1), mixedCharacter F (1, b)) = (a, b) ∧
    (firstInverseCharacter F (a, 1), firstInverseCharacter F (1, b)) = (a⁻¹, 1) ∧
    (secondInverseCharacter F (a, 1), secondInverseCharacter F (1, b)) = (1, b⁻¹) := by
  simp [mixedCharacter, firstInverseCharacter, secondInverseCharacter]

/-- The simultaneous direct-sum comparison is the chosen free-module isomorphism,
not an equality of the three summands with the labelled free object. -/
def rankThreeToFree : ((rankThreeRow F).obj (SingleObj.star _)).of ≅
    free (R := Fᵐᵒᵖ) 3 :=
  biprod.mapIso (Iso.refl (free (R := Fᵐᵒᵖ) 1)) (freeSuccIso (R := Fᵐᵒᵖ) 1) ≪≫
    freeSuccIso (R := Fᵐᵒᵖ) 2

/-- The prescribed power-to-free isomorphism remains visible in the rank-three join. -/
def rankThreeToPower : (rankThreeRow F).obj (SingleObj.star _) ≅ rankOnePower Fᵐᵒᵖ 3 :=
  Core.isoMk (rankThreeToFree F) ≪≫ (rankOnePowerIsoFree Fᵐᵒᵖ 3).symm

/-- The loop map obtained from the zero and full cones of a row. -/
def rowLoop (A : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ) :=
  ConePair.naturalPair (zeroCone (exactStructure Fᵐᵒᵖ) A)
    (fullCone (exactStructure Fᵐᵒᵖ) A)

/-- The actual whole rank-three Q-cone family splits on the same common groupoid. -/
def rankThreeConeHomotopy :
    (rowLoop F (rankThreeRow F)).Homotopy
      (concatenate (rowLoop F (row2 F))
        (concatenate (rowLoop F (row1 F)) (rowLoop F (row0 F)))) :=
  (biprodCoreLoopHomotopy (exactStructure Fᵐᵒᵖ) (row2 F)
    (biprodCore (row1 F) (row0 F))).trans
      (concatenateHomotopy (ContinuousMap.Homotopy.refl (rowLoop F (row2 F)))
        (biprodCoreLoopHomotopy (exactStructure Fᵐᵒᵖ) (row1 F) (row0 F)))

/-- Joint normalization preserves all torus coordinates and the moving cancellation cap. -/
def normalizedRankThreeConeHomotopy :
    (Automorphism.rightNormalizedLoopMap (rowLoop F (rankThreeRow F))
      (classifyingSpacePoint (SingleObj.star _))).Homotopy
    (Automorphism.rightNormalizedLoopMap
      (concatenate (rowLoop F (row2 F))
        (concatenate (rowLoop F (row1 F)) (rowLoop F (row0 F))))
      (classifyingSpacePoint (SingleObj.star _))) :=
  Automorphism.rightNormalizedHomotopy (rankThreeConeHomotopy F)
    (classifyingSpacePoint (SingleObj.star _))

/-- The literal diagonal matrix representation of the same product group. -/
def diagonalRepresentation : (Fˣ × Fˣ) →* Matrix.GeneralLinearGroup (Fin 3) F where
  toFun z :=
    { val := Matrix.diagonal ![((z.1 * z.2 : Fˣ) : F), ((z.1⁻¹ : Fˣ) : F), ((z.2⁻¹ : Fˣ) : F)]
      inv := Matrix.diagonal ![(((z.1 * z.2)⁻¹ : Fˣ) : F), (z.1 : F), (z.2 : F)]
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_assoc]
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_assoc] }
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' z w := by
    apply Units.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_inv_rev, mul_comm, mul_left_comm]

theorem diagonalRepresentation_first (a : Fˣ) :
    (diagonalRepresentation F (a, 1)).val =
      Matrix.diagonal ![(a : F), ((a⁻¹ : Fˣ) : F), 1] := by
  simp [diagonalRepresentation]

theorem diagonalRepresentation_second (b : Fˣ) :
    (diagonalRepresentation F (1, b)).val =
      Matrix.diagonal ![(b : F), 1, ((b⁻¹ : Fˣ) : F)] := by
  simp [diagonalRepresentation]

/-- The two source loops commute before realization, with their ordered matrices retained. -/
theorem diagonalRepresentation_commute (a b : Fˣ) :
    Commute (diagonalRepresentation F (a, 1)) (diagonalRepresentation F (1, b)) :=
  (Commute.all (a, (1 : Fˣ)) ((1 : Fˣ), b)).map (diagonalRepresentation F)

/-- A central source element gives its genuine identity natural transformation. -/
def sourceTransformation (g : Fˣ × Fˣ) : 𝟭 (TorusSource F) ⟶ 𝟭 (TorusSource F) where
  app _ := (SingleObj.toEnd _ g).asHom
  naturality {X Y} f := by
    cases X
    cases Y
    simp only [Functor.id_map, SingleObj.comp_as_mul, SingleObj.toEnd_def]
    exact mul_comm (g : Fˣ × Fˣ) f

/-- The source self-homotopy induced by a unit pair. -/
def sourceHomotopy (g : Fˣ × Fˣ) :
    (ContinuousMap.id (ClassifyingSpace (TorusSource F))).Homotopy
      (ContinuousMap.id (ClassifyingSpace (TorusSource F))) :=
  (classifyingSpaceNaturalTransformationHomotopy (sourceTransformation F g)).cast
    (congrArg TopCat.Hom.hom (classifyingSpaceMap_id (C := TorusSource F)))
    (congrArg TopCat.Hom.hom (classifyingSpaceMap_id (C := TorusSource F)))

/-- The based source edge induced by a unit pair. -/
def sourceEdge (g : Fˣ × Fˣ) :
    Path (classifyingSpacePoint (SingleObj.star (Fˣ × Fˣ)))
      (classifyingSpacePoint (SingleObj.star (Fˣ × Fˣ))) :=
  classifyingSpacePath (SingleObj.toEnd _ g).asHom

theorem sourceHomotopy_vertex (g : Fˣ × Fˣ) (t : unitInterval) :
    sourceHomotopy F g (t, classifyingSpacePoint (SingleObj.star _)) = sourceEdge F g t := by
  simpa [sourceHomotopy, sourceEdge, sourceTransformation] using
    classifyingSpaceNaturalTransformationHomotopy_vertex_general (sourceTransformation F g)
      (SingleObj.star _) t

/-- The raw two-time torus is an actual categorical cylinder on the second edge. -/
def rawTorus (a b : Fˣ) : C(unitInterval × unitInterval, ClassifyingSpace (TorusSource F)) where
  toFun z := sourceHomotopy F (a, 1) (z.1, sourceEdge F (1, b) z.2)
  continuous_toFun := (sourceHomotopy F (a, 1)).continuous.comp
    (continuous_fst.prodMk ((sourceEdge F (1, b)).continuous.comp continuous_snd))

theorem rawTorus_zero_first (a b : Fˣ) (s : unitInterval) :
    rawTorus F a b (0,s) = sourceEdge F (1,b) s :=
  (sourceHomotopy F (a,1)).apply_zero _

theorem rawTorus_one_first (a b : Fˣ) (s : unitInterval) :
    rawTorus F a b (1,s) = sourceEdge F (1,b) s :=
  (sourceHomotopy F (a,1)).apply_one _

theorem rawTorus_zero_second (a b : Fˣ) (t : unitInterval) :
    rawTorus F a b (t,0) = sourceEdge F (a,1) t := by
  change sourceHomotopy F (a,1) (t, sourceEdge F (1,b) 0) = _
  rw [Path.source, sourceHomotopy_vertex]

theorem rawTorus_one_second (a b : Fˣ) (t : unitInterval) :
    rawTorus F a b (t,1) = sourceEdge F (a,1) t := by
  change sourceHomotopy F (a,1) (t, sourceEdge F (1,b) 1) = _
  rw [Path.target, sourceHomotopy_vertex]

/-- The source character is the same scalar automorphism on the original projective,
including the opposite-unit transport and the original reversed matrix action. -/
theorem scalarRow_component (χ : (Fˣ × Fˣ) →* Fˣ) (g : Fˣ × Fˣ) :
    ((scalarRow F χ).map (SingleObj.toEnd _ g).asHom).iso =
      ((CategoryTheory.Linear.scalarNatAut Fᵐᵒᵖ (ModuleCat.FiniteProjective.Category.{u, u} Fᵐᵒᵖ)
        (FGModuleCat.SymbolMarking.opUnit F (χ g))).asIso).app (free (R := Fᵐᵒᵖ) 1) := by
  apply Iso.ext
  apply (ModuleCat.FiniteProjective.property Fᵐᵒᵖ).ι.map_injective
  change (ModuleCat.FiniteProjective.property Fᵐᵒᵖ).ι.map
    (Matrix.RightModule.leftFreeAutEquiv F 1
        (Matrix.GeneralLinearGroup.scalar (Fin 1) (χ g))).asIso.hom = _
  rw [show (ModuleCat.FiniteProjective.property Fᵐᵒᵖ).ι.map
      (Matrix.RightModule.leftFreeAutEquiv F 1
        (Matrix.GeneralLinearGroup.scalar (Fin 1) (χ g))).asIso.hom =
        (Matrix.RightModule.leftModuleAutEquiv F 1
          (Matrix.GeneralLinearGroup.scalar (Fin 1) (χ g))).asIso.hom from
      congrArg Iso.hom (Matrix.RightModule.leftFreeAutEquiv_map F 1 _)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  exact FGModuleCat.SymbolMarking.left_right_scalar_matrix_apply F 1 (χ g) x i

theorem row0_first_component (a : Fˣ) :
    ((row0 F).map (SingleObj.toEnd _ (a, (1 : Fˣ))).asHom).iso =
      ((CategoryTheory.Linear.scalarNatAut Fᵐᵒᵖ (ModuleCat.FiniteProjective.Category.{u, u} Fᵐᵒᵖ)
        (FGModuleCat.SymbolMarking.opUnit F a)).asIso).app (free (R := Fᵐᵒᵖ) 1) := by
  simpa [row0, mixedCharacter] using scalarRow_component F (mixedCharacter F) (a, 1)

/-- Both varying source parameters are carried by the actual scalar natural transformation. -/
theorem scalarRow_transformation (χ : (Fˣ × Fˣ) →* Fˣ) (g : Fˣ × Fˣ) :
    Functor.whiskerRight (sourceTransformation F g) (scalarRow F χ) =
      Functor.whiskerLeft (scalarRow F χ)
        (Equivariance.identityCoreAction.{u +
          1, u}
          ((CategoryTheory.Linear.scalarNatAut Fᵐᵒᵖ (ModuleCat.FiniteProjective.Category.{u, u}
            Fᵐᵒᵖ)
            (FGModuleCat.SymbolMarking.opUnit F (χ g))).asIso)) := by
  apply NatTrans.ext
  funext X
  cases X
  apply Core.hom_ext
  exact congrArg Iso.hom (scalarRow_component F χ g)

theorem diagonalRepresentation_eq (g : Fˣ × Fˣ) :
    diagonalRepresentation F g = FGModuleCat.SymbolMarking.Diagonal.diagonalUnit F 3
      (Fin.snoc (Fin.snoc (fun _ : Fin 1 => g.1 * g.2) g.1⁻¹) g.2⁻¹) := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The simultaneous rank-three sum acts by the literal diagonal matrices under
the original free-successor isomorphisms and reversed ordered basis. -/
theorem rankThreeToFree_naturality (g : Fˣ × Fˣ) :
    ((rankThreeRow F).map (SingleObj.toEnd _ g).asHom).iso.hom ≫ (rankThreeToFree F).hom =
      (rankThreeToFree F).hom ≫
        (Matrix.RightModule.leftFreeAutEquiv F 3 (diagonalRepresentation F g)).asIso.hom := by
  let d : Fin 1 → Fˣ := fun _ => g.1 * g.2
  let d' : Fin 2 → Fˣ := Fin.snoc d g.1⁻¹
  let A := Matrix.RightModule.leftFreeAutEquiv F 1
    (FGModuleCat.SymbolMarking.Diagonal.diagonalUnit F 1 (fun _ => g.2⁻¹))
  let B := Matrix.RightModule.leftFreeAutEquiv F 1
    (FGModuleCat.SymbolMarking.Diagonal.diagonalUnit F 1 (fun _ => g.1⁻¹))
  let C := Matrix.RightModule.leftFreeAutEquiv F 1
    (FGModuleCat.SymbolMarking.Diagonal.diagonalUnit F 1 d)
  let D := Matrix.RightModule.leftFreeAutEquiv F 2
    (FGModuleCat.SymbolMarking.Diagonal.diagonalUnit F 2 d')
  let e₁ := freeSuccIso (R := Fᵐᵒᵖ) 1
  let e₂ := freeSuccIso (R := Fᵐᵒᵖ) 2
  have h₁ : biprod.map B.asIso.hom C.asIso.hom ≫ e₁.hom = e₁.hom ≫ D.asIso.hom :=
    FGModuleCat.SymbolMarking.Diagonal.diagonalUnit_free_prepend_natural F 1 d g.1⁻¹
  have h₂ := FGModuleCat.SymbolMarking.Diagonal.diagonalUnit_free_prepend_natural F 2 d' g.2⁻¹
  have hmap : biprod.map A.asIso.hom (biprod.map B.asIso.hom C.asIso.hom) ≫ biprod.map (𝟙 _)
    e₁.hom =
      biprod.map (𝟙 _) e₁.hom ≫ biprod.map A.asIso.hom D.asIso.hom := by
    apply biprod.hom_ext
    · simp
    · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc]
      rw [h₁]
  rw [diagonalRepresentation_eq]
  change biprod.map A.asIso.hom (biprod.map B.asIso.hom C.asIso.hom) ≫
    (biprod.map (𝟙 _) e₁.hom ≫ e₂.hom) =
      (biprod.map (𝟙 _) e₁.hom ≫ e₂.hom) ≫
        (Matrix.RightModule.leftFreeAutEquiv F 3
          (FGModuleCat.SymbolMarking.Diagonal.diagonalUnit F 3 (Fin.snoc d' g.2⁻¹))).asIso.hom
  rw [← Category.assoc, hmap, Category.assoc, h₂, Category.assoc]

/-- The rank-three representation viewed as a free power row. -/
def matrixPowerRow : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ :=
  (diagonalRepresentation F).toFunctor ⋙ StableFree.powerFunctor F 3

/-- The exact actual power-basis conjugacy is natural for the whole two-parameter source. -/
def rankThreePowerNatIso : rankThreeRow F ≅ matrixPowerRow F :=
  NatIso.ofComponents (fun _ => rankThreeToPower F) (by
    intro X Y g
    cases X
    cases Y
    let e := Core.isoMk (rankThreeToFree F)
    let r := rankOnePowerIsoFree Fᵐᵒᵖ 3
    have he : (rankThreeRow F).map g ≫ e.hom =
        e.hom ≫ (StableFree.freeEndEquiv F 3 (diagonalRepresentation F g)).asHom := by
      apply Core.hom_ext
      exact rankThreeToFree_naturality F g
    change (rankThreeRow F).map g ≫ (e.hom ≫ r.inv) =
      (e.hom ≫ r.inv) ≫
        (r.hom ≫ (StableFree.freeEndEquiv F 3 (diagonalRepresentation F g)).asHom ≫ r.inv)
    rw [← Category.assoc, he]
    simp [Category.assoc])

/-- Whole-source Q-cone comparison retains the simultaneous original power-basis conjugacy. -/
def rankThreePowerConeHomotopy :
    (rowLoop F (matrixPowerRow F)).Homotopy (rowLoop F (rankThreeRow F)) :=
  (coreIsoLoopHomotopy (exactStructure Fᵐᵒᵖ) (rankThreeRow F) (matrixPowerRow F)
    (rankThreePowerNatIso F)).symm

theorem rowLoop_eq (A : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ) :
    rowLoop F A = (Automorphism.universalCoreLoopMap (exactStructure Fᵐᵒᵖ)).comp
      (classifyingSpaceMapUniversal A) := by
  ext z t
  change ((ConePair.realizedCone (zeroCone (exactStructure Fᵐᵒᵖ) A)).evalAt z).trans
      ((ConePair.realizedCone (fullCone (exactStructure Fᵐᵒᵖ) A)).evalAt z).symm t =
    ((ConePair.realizedCone (Automorphism.zeroCone (exactStructure Fᵐᵒᵖ))).evalAt
      (classifyingSpaceMapUniversal A z)).trans
      ((ConePair.realizedCone (Automorphism.fullCone (exactStructure Fᵐᵒᵖ))).evalAt
        (classifyingSpaceMapUniversal A z)).symm t
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact universalHomotopy_whiskerLeft A (Automorphism.zeroCone (exactStructure Fᵐᵒᵖ)) _ z
  · exact universalHomotopy_whiskerLeft A (Automorphism.fullCone (exactStructure Fᵐᵒᵖ)) _ z

/-- The rank-three representation in the original finite matrix stage. -/
def matrixStageRow : TorusSource F ⥤ StableGeneralLinear.finiteCategory F 3 :=
  (diagonalRepresentation F).toFunctor ⋙ AsSmall.up

theorem powerRowLoop_stage :
    rowLoop F (matrixPowerRow F) =
      (stageCoreLoopMap F 3).comp (classifyingSpaceMapUniversal (matrixStageRow F)) := by
  rw [rowLoop_eq]
  unfold stageCoreLoopMap
  rw [ContinuousMap.comp_assoc, ← classifyingSpaceMapUniversal_comp]
  rfl

/-- The original stage-three loop map of the matrix row. -/
def nativeRankThreeLoopMap :=
  (nativeStageLoopMap F 3).comp (classifyingSpaceMapUniversal (matrixStageRow F))

/-- The actual native completion map on the whole diagonal source has its original
full-first normalization, not just its induced K-one class. -/
def nativeRankThreePowerHomotopy :
    (nativeRankThreeLoopMap F).Homotopy
      (Automorphism.rightNormalizedLoopMap
        (loopReversal.comp (rowLoop F (matrixPowerRow F)))
        (classifyingSpacePoint (SingleObj.star _))) := by
  let H := (nativeStageCoreHomotopy F 3).compContinuousMap
    (classifyingSpaceMapUniversal (matrixStageRow F))
  refine H.cast rfl ?_
  have hbase : classifyingSpaceMapUniversal (matrixStageRow F)
      (classifyingSpacePoint (SingleObj.star _)) = classifyingSpacePoint (stageVertex F 3) :=
    classifyingSpaceMapUniversal_point (matrixStageRow F) _
  rw [powerRowLoop_stage]
  ext z t
  change ((stageCoreLoopMap F 3
    (classifyingSpaceMapUniversal (matrixStageRow F) z)).symm.trans
      (stageCoreLoopMap F 3 (classifyingSpacePoint (stageVertex F 3))).symm.symm) t =
    ((stageCoreLoopMap F 3
      (classifyingSpaceMapUniversal (matrixStageRow F) z)).symm.trans
        (stageCoreLoopMap F 3 (classifyingSpaceMapUniversal (matrixStageRow F)
          (classifyingSpacePoint (SingleObj.star _)))).symm.symm) t
  rw [hbase]

/-- The original completion comparison reaches the whole three-summand Q family,
retaining the moving normalization cap, actual matrix source and power-basis conjugacy. -/
def nativeRankThreeSplitHomotopy :
    (nativeRankThreeLoopMap F).Homotopy
      (Automorphism.rightNormalizedLoopMap
        (loopReversal.comp (concatenate (rowLoop F (row2 F))
          (concatenate (rowLoop F (row1 F)) (rowLoop F (row0 F)))))
        (classifyingSpacePoint (SingleObj.star _))) :=
  (nativeRankThreePowerHomotopy F).trans
    (Automorphism.rightNormalizedHomotopy
      ((ContinuousMap.Homotopy.refl loopReversal).comp
        ((rankThreePowerConeHomotopy F).trans (rankThreeConeHomotopy F)))
      (classifyingSpacePoint (SingleObj.star _)))

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped Topology unitInterval

universe u

namespace FGModuleCat.SymbolMarking
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
open FGModuleCat.SymbolMarking
  ModuleCat.FiniteProjective

variable (F : Type u) [Field F]

/-- The periodic source square determined by the ordered unit pair. -/
def sourceTorus (a b : Fˣ) : PeriodicSquare (ClassifyingSpace (TorusSource F)) :=
  ⟨rawTorus F a b,
    (fun s => (rawTorus_zero_first F a b s).trans (rawTorus_one_first F a b s).symm),
    (fun t => (rawTorus_zero_second F a b t).trans (rawTorus_one_second F a b t).symm)⟩

/-- The periodic loop family obtained by mapping the source torus. -/
def sourceLoopFamily (a b : Fˣ)
    (f : C(ClassifyingSpace (TorusSource F),
      Path (exactStructure Fᵐᵒᵖ).kBasepoint (exactStructure Fᵐᵒᵖ).kBasepoint)) :=
  periodicPost f (sourceTorus F a b)

/-- The periodic loop class of the mapped source torus. -/
def sourceLoopClass (a b : Fˣ)
    (f : C(ClassifyingSpace (TorusSource F),
      Path (exactStructure Fᵐᵒᵖ).kBasepoint (exactStructure Fᵐᵒᵖ).kBasepoint)) :=
  periodicClass (sourceLoopFamily F a b f)

theorem sourceLoopClass_homotopy (a b : Fˣ)
    {f g : C(ClassifyingSpace (TorusSource F),
      Path (exactStructure Fᵐᵒᵖ).kBasepoint (exactStructure Fᵐᵒᵖ).kBasepoint)}
    (H : f.Homotopy g) : sourceLoopClass F a b f = sourceLoopClass F a b g :=
  periodicClass_of_path (periodicPostHomotopy H (sourceTorus F a b))

theorem sourceLoopClass_concat (a b : Fˣ)
    (f g : C(ClassifyingSpace (TorusSource F),
      Path (exactStructure Fᵐᵒᵖ).kBasepoint (exactStructure Fᵐᵒᵖ).kBasepoint)) :
    sourceLoopClass F a b (concatenate f g) =
      sourceLoopClass F a b f * sourceLoopClass F a b g := by
  have h : sourceLoopFamily F a b (concatenate f g) =
      periodicConcat (sourceLoopFamily F a b f) (sourceLoopFamily F a b g) := by
    apply Subtype.ext
    ext z q
    rfl
  change periodicClass (sourceLoopFamily F a b (concatenate f g)) = _
  rw [h, periodicClass_concat]
  rfl

theorem sourceLoopClass_reverse (a b : Fˣ)
    (f : C(ClassifyingSpace (TorusSource F),
      Path (exactStructure Fᵐᵒᵖ).kBasepoint (exactStructure Fᵐᵒᵖ).kBasepoint)) :
    sourceLoopClass F a b (loopReversal.comp f) = (sourceLoopClass F a b f)⁻¹ := by
  have h : sourceLoopFamily F a b (loopReversal.comp f) =
      periodicReverse (sourceLoopFamily F a b f) := by
    apply Subtype.ext
    ext z q
    rfl
  change periodicClass (sourceLoopFamily F a b (loopReversal.comp f)) = _
  rw [h, periodicClass_reverse]
  rfl

/-- The actual source commutation prism gives commutation of periodic classes.
This uses neither a stationary vertex nor a blanket commutativity hypothesis. -/
theorem sourceRows_commute (a b : Fˣ) (L R : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ) :
    Commute (sourceLoopClass F a b (rowLoop F L))
      (sourceLoopClass F a b (rowLoop F R)) := by
  change _ * _ = _ * _
  rw [← sourceLoopClass_concat, ← sourceLoopClass_concat]
  exact sourceLoopClass_homotopy F a b (coreLoopCommutation (exactStructure Fᵐᵒᵖ) L R)

/-- The native source reaches the periodic homotopy group through its ACTUAL
whole-source splitting, with no assertion about either cap. -/
theorem native_periodic_class (a b : Fˣ) :
    sourceLoopClass F a b (nativeRankThreeLoopMap F) =
      sourceLoopClass F a b
        (Automorphism.rightNormalizedLoopMap
          (loopReversal.comp (concatenate (rowLoop F (row2 F))
            (concatenate (rowLoop F (row1 F)) (rowLoop F (row0 F)))))
          (classifyingSpacePoint (SingleObj.star _))) :=
  sourceLoopClass_homotopy F a b (nativeRankThreeSplitHomotopy F)

/-- The original rank-one object loop at the shared actual vertex. -/
def sourceObjectLoop :=
  Automorphism.universalCoreLoopMap (exactStructure Fᵐᵒᵖ)
    (classifyingSpacePoint (freeIso Fᵐᵒᵖ 1))

theorem scalarRow_loop_vertex (χ : (Fˣ × Fˣ) →* Fˣ) :
    rowLoop F (scalarRow F χ) (classifyingSpacePoint (SingleObj.star _)) =
      sourceObjectLoop F := by
  rw [rowLoop_eq]
  change Automorphism.universalCoreLoopMap (exactStructure Fᵐᵒᵖ)
    (classifyingSpaceMapUniversal (scalarRow F χ)
      (classifyingSpacePoint (SingleObj.star _))) = _
  rw [classifyingSpaceMapUniversal_point]
  rfl

/-- The constant free rank-one row. -/
def constantRow : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ :=
  (Functor.const _).obj (freeIso Fᵐᵒᵖ 1)

theorem constantRow_loop : rowLoop F (constantRow F) =
    ContinuousMap.const _ (sourceObjectLoop F) := by
  rw [rowLoop_eq]
  unfold constantRow
  rw [classifyingSpaceMapUniversal_const]
  rfl

/-- The exact constant object-loop factor commutes by the same actual braiding prism. -/
theorem sourceRows_object_commute (a b : Fˣ) (L : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ) :
    Commute (sourceLoopClass F a b (rowLoop F L))
      (sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F))) := by
  rw [← constantRow_loop]
  exact sourceRows_commute F a b L (constantRow F)

/-- The precise ordered word of the native periodic family before attaching axis caps. -/
theorem native_periodic_word (a b : Fˣ) :
    sourceLoopClass F a b (nativeRankThreeLoopMap F) =
      (sourceLoopClass F a b (rowLoop F (row2 F)) *
        (sourceLoopClass F a b (rowLoop F (row1 F)) *
          sourceLoopClass F a b (rowLoop F (row0 F))))⁻¹ *
      (sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F)) *
        (sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F)) *
          sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F)))) := by
  rw [native_periodic_class]
  let L := concatenate (rowLoop F (row2 F))
    (concatenate (rowLoop F (row1 F)) (rowLoop F (row0 F)))
  have hv : L (classifyingSpacePoint (SingleObj.star _)) =
      (sourceObjectLoop F).trans ((sourceObjectLoop F).trans (sourceObjectLoop F)) := by
    change (rowLoop F (row2 F) _).trans
      ((rowLoop F (row1 F) _).trans (rowLoop F (row0 F) _)) = _
    rw [show row2 F = scalarRow F (secondInverseCharacter F) from rfl,
      show row1 F = scalarRow F (firstInverseCharacter F) from rfl,
      show row0 F = scalarRow F (mixedCharacter F) from rfl,
      scalarRow_loop_vertex, scalarRow_loop_vertex, scalarRow_loop_vertex]
  have hmap : Automorphism.rightNormalizedLoopMap (loopReversal.comp L)
      (classifyingSpacePoint (SingleObj.star _)) =
      concatenate (loopReversal.comp L)
        (concatenate (ContinuousMap.const _ (sourceObjectLoop F))
          (concatenate (ContinuousMap.const _ (sourceObjectLoop F))
            (ContinuousMap.const _ (sourceObjectLoop F)))) := by
    ext z q
    change ((L z).symm.trans (L (classifyingSpacePoint (SingleObj.star _))).symm.symm) q = _
    rw [Path.symm_symm, hv]
    rfl
  change sourceLoopClass F a b (Automorphism.rightNormalizedLoopMap
    (loopReversal.comp L) (classifyingSpacePoint (SingleObj.star _))) = _
  rw [hmap, sourceLoopClass_concat, sourceLoopClass_reverse]
  dsimp only [L]
  simp only [sourceLoopClass_concat]

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped Topology unitInterval

universe u

namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective

variable (F : Type u) [Field F]

theorem sourceHomotopy_one (t : unitInterval) (z : ClassifyingSpace (TorusSource F)) :
    sourceHomotopy F 1 (t,z) = z := by
  have h : sourceTransformation F 1 = 𝟙 (𝟭 (TorusSource F)) := by
    apply NatTrans.ext
    funext X
    cases X
    rfl
  change classifyingSpaceNaturalTransformationHomotopy (sourceTransformation F 1) (t,z) = _
  rw [h]
  exact Cylinder.identity_track t z

theorem sourceEdge_one : sourceEdge F 1 = Path.refl (classifyingSpacePoint (SingleObj.star _)) := by
  change classifyingSpacePath (𝟙 (SingleObj.star (Fˣ × Fˣ))) = _
  exact classifyingSpacePath_id _

theorem sourceHomotopy_map (h : (Fˣ × Fˣ) →* (Fˣ × Fˣ)) (g : Fˣ × Fˣ)
    (t : unitInterval) (z : ClassifyingSpace (TorusSource F)) :
    classifyingSpaceMap h.toFunctor (sourceHomotopy F g (t,z)) =
      sourceHomotopy F (h g) (t,classifyingSpaceMap h.toFunctor z) := by
  have he : Functor.whiskerRight (sourceTransformation F g) h.toFunctor =
      Functor.whiskerLeft h.toFunctor (sourceTransformation F (h g)) := by
    apply NatTrans.ext
    funext X
    cases X
    rfl
  change classifyingSpaceMap h.toFunctor
    (classifyingSpaceNaturalTransformationHomotopy (sourceTransformation F g) (t,z)) =
      classifyingSpaceNaturalTransformationHomotopy (sourceTransformation F (h g))
        (t,classifyingSpaceMap h.toFunctor z)
  rw [← Cylinder.classifyingSpaceNaturalTransformationHomotopy_whiskerRight, he,
    Cylinder.classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]

theorem sourceEdge_map (h : (Fˣ × Fˣ) →* (Fˣ × Fˣ)) (g : Fˣ × Fˣ)
    (s : unitInterval) :
    classifyingSpaceMap h.toFunctor (sourceEdge F g s) = sourceEdge F (h g) s := by
  change classifyingSpaceMap h.toFunctor
    (classifyingSpacePath (C := TorusSource F) (SingleObj.toEnd (Fˣ × Fˣ) g).asHom s) = _
  rw [classifyingSpacePath_naturality]
  rfl

theorem rawTorus_map (h : (Fˣ × Fˣ) →* (Fˣ × Fˣ)) (a b : Fˣ)
    (t s : unitInterval) :
    classifyingSpaceMap h.toFunctor (rawTorus F a b (t,s)) =
      sourceHomotopy F (h (a,1)) (t, sourceEdge F (h (1,b)) s) := by
  change classifyingSpaceMap h.toFunctor
    (sourceHomotopy F (a,1) (t, sourceEdge F (1,b) s)) = _
  rw [sourceHomotopy_map, sourceEdge_map]

/-- The source endomorphism retaining only the first unit coordinate. -/
def firstProjection : (Fˣ × Fˣ) →* (Fˣ × Fˣ) := (MonoidHom.fst Fˣ Fˣ).prod 1
/-- The source endomorphism retaining only the second unit coordinate. -/
def secondProjection : (Fˣ × Fˣ) →* (Fˣ × Fˣ) := (1 : (Fˣ × Fˣ) →* Fˣ).prod (MonoidHom.snd Fˣ Fˣ)

theorem firstProjection_torus (a b : Fˣ) (t s : unitInterval) :
    classifyingSpaceMap (firstProjection F).toFunctor (rawTorus F a b (t,s)) =
      sourceEdge F (a,1) t := by
  rw [rawTorus_map]
  change sourceHomotopy F (a,1) (t,sourceEdge F 1 s) = _
  rw [sourceEdge_one]
  exact sourceHomotopy_vertex F (a,1) t

theorem secondProjection_torus (a b : Fˣ) (t s : unitInterval) :
    classifyingSpaceMap (secondProjection F).toFunctor (rawTorus F a b (t,s)) =
      sourceEdge F (1,b) s := by
  rw [rawTorus_map]
  change sourceHomotopy F 1 (t,sourceEdge F (1,b) s) = _
  exact sourceHomotopy_one F t _

theorem scalarRow_precomp (h : (Fˣ × Fˣ) →* (Fˣ × Fˣ))
    (χ : (Fˣ × Fˣ) →* Fˣ) :
    h.toFunctor ⋙ scalarRow F χ = scalarRow F (χ.comp h) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y g
  cases X
  cases Y
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

theorem scalarRow_loop_precomp (h : (Fˣ × Fˣ) →* (Fˣ × Fˣ))
    (χ : (Fˣ × Fˣ) →* Fˣ) (z : ClassifyingSpace (TorusSource F)) :
    rowLoop F (scalarRow F χ) (classifyingSpaceMap h.toFunctor z) =
      rowLoop F (scalarRow F (χ.comp h)) z := by
  have hh := congrArg (fun m => m z)
    (classifyingSpaceMapUniversal_comp h.toFunctor (scalarRow F χ))
  rw [scalarRow_precomp] at hh
  have hm : classifyingSpaceMapUniversal h.toFunctor z = classifyingSpaceMap h.toFunctor z :=
    congrArg (fun m => m z) (classifyingSpaceMapUniversal_eq h.toFunctor)
  have he : classifyingSpaceMapUniversal (scalarRow F χ) (classifyingSpaceMap h.toFunctor z) =
      classifyingSpaceMapUniversal (scalarRow F (χ.comp h)) z := by
    change _ = _ at hh
    simpa only [ContinuousMap.comp_apply, hm] using hh.symm
  rw [rowLoop_eq, rowLoop_eq]
  exact congrArg (Automorphism.universalCoreLoopMap (exactStructure Fᵐᵒᵖ)) he

/-- The first inverse row is literally independent of the second torus parameter. -/
theorem row1_torus (a b : Fˣ) (t s : unitInterval) :
    rowLoop F (row1 F) (rawTorus F a b (t,s)) =
      rowLoop F (row1 F) (sourceEdge F (a,1) t) := by
  have hc : (firstInverseCharacter F).comp (firstProjection F) = firstInverseCharacter F := by
    ext g
    rfl
  have h := scalarRow_loop_precomp F (firstProjection F) (firstInverseCharacter F)
    (rawTorus F a b (t,s))
  rw [hc, firstProjection_torus] at h
  exact h.symm

/-- The second inverse row is literally independent of the first torus parameter. -/
theorem row2_torus (a b : Fˣ) (t s : unitInterval) :
    rowLoop F (row2 F) (rawTorus F a b (t,s)) =
      rowLoop F (row2 F) (sourceEdge F (1,b) s) := by
  have hc : (secondInverseCharacter F).comp (secondProjection F) = secondInverseCharacter F := by
    ext g
    rfl
  have h := scalarRow_loop_precomp F (secondProjection F) (secondInverseCharacter F)
    (rawTorus F a b (t,s))
  rw [hc, secondProjection_torus] at h
  exact h.symm

end FGModuleCat.SymbolMarking

end

end
