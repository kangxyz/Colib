/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.RingTheory.KTheory.Quillen.Field.PositiveSymbolMarking
import Colib.Topology.Homotopy.HomotopyGroup.PeriodicLoopFamilies
import Mathlib.Algebra.Field.ZMod

/-! Regression checks for the original positive unit product, its actual caps and
coordinate signs. The ordered marking is tested over arbitrary fields and in
positive characteristic, independently of the characteristic-zero equivalence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.ExactCategory Topology
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
open scoped unitInterval commutatorElement
attribute [local instance] Abelian.hasFiniteBiproducts
universe u v

-- The original product is the scalar identity action on the determinant's literal inverse.
example (F : Type u) [Field F] (a b : Fˣ) :
    FGModuleCat.FieldSymbols.unitProduct F a b =
      ScalarUnit.upperFiniteModuleKOneAction F a ((FGModuleCat.moduleDetEquiv F).symm b) := rfl

example (F : Type u) [Field F] (a b : Fˣ) :
    MilnorKTheory.toUpperModuleKTwo F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct F a b) :=
  MilnorKTheory.toUpperModuleKTwo_pair_eq_unitProduct F a b

example (a b : (ZMod 5)ˣ) :
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    MilnorKTheory.toUpperModuleKTwo (ZMod 5) (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct (ZMod 5) a b) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact MilnorKTheory.toUpperModuleKTwo_pair_eq_unitProduct (ZMod 5) a b

example {F L : Type u} [Field F] [Field L] (f : F →+* L) (a b : Fˣ) :
    (FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2
      (FGModuleCat.FieldSymbols.unitProduct F a b) =
        FGModuleCat.FieldSymbols.unitProduct L
          (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) :=
  FGModuleCat.FieldSymbols.unitProduct_natural f a b

-- The first inverse is the actual scalar cube's coordinate transposition.
example (F : Type u) [Field F] (a b : Fˣ) :
    (loopShiftMulEquiv (x := (exactStructure Fᵐᵒᵖ).kBasepoint) 1).symm
      (Quotient.mk' (scalarLoopCube F a b)) = (scalarClass F a b)⁻¹ :=
  scalarLoopCube_originalClass F a b

-- The actual connecting boundary cancels that inverse without reversing the ordered lifts.
example (F : Type u) [Field F] (a b : Fˣ) :
    kTwoToFiber F (scalarClass F a b) =
      ⁅firstGeometricLift F a b, secondGeometricLift F a b⁆ :=
  scalarClass_boundary_commutator F a b

-- The raw periodic input uses the original outer/inner coordinates, without a loop reversal.
example {X : Type u} [TopologicalSpace X] {x : X}
    (q : Path (Path.refl x) (Path.refl x)) (r s : unitInterval) :
    inputCube q ![r, s] = q s r := rfl

-- The retained object loop is literally zero edge followed by the inverse full edge.
example (F : Type u) [Field F] : sourceObjectLoop F =
    ((ConePair.realizedCone (Automorphism.zeroCone (exactStructure Fᵐᵒᵖ))).evalAt
      (classifyingSpacePoint (freeIso Fᵐᵒᵖ 1))).trans
    ((ConePair.realizedCone (Automorphism.fullCone (exactStructure Fᵐᵒᵖ))).evalAt
      (classifyingSpacePoint (freeIso Fᵐᵒᵖ 1))).symm := rfl

-- The chosen original relative cap is retained with both endpoint casts and double base loop.
example {X : Type u} [TopologicalSpace X] {x : X}
    {Z : Type v} [TopologicalSpace Z] (f : C(Z, Path x x)) (z : Z)
    (H : (⟨fun w => (f z).trans (f w), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun w => (f w).trans (f z), by fun_prop⟩)
    (p : Path x x) (hp : f z = p) (δ : Path z z)
    (hcap : (pointwiseLoopProduct ((δ.map f.continuous).cast hp.symm hp.symm)
      ((δ.map f.continuous).cast hp.symm hp.symm).symm).Homotopic
        (Path.refl (p.trans p))) :
    inverseAxisCap f z H p hp δ = hcap.some :=
  inverseAxisCap_eq_some f z H p hp δ hcap

-- An explicit moving vertex supplies the actual inverse-axis cap; stationarity is not assumed.
example :
    let f : C(Unit, Path (0 : ℝ) 0) := ContinuousMap.const _ (Path.refl 0)
    ∃ H : (⟨fun w => (f ()).trans (f w), by fun_prop⟩ :
        C(Unit, Path (0 : ℝ) 0)).Homotopy
        ⟨fun w => (f w).trans (f ()), by fun_prop⟩,
      H (⟨1 / 2, by norm_num⟩, ()) ⟨1 / 2, by norm_num⟩ = (1 : ℝ) / 16 ∧
        Nonempty ((pointwiseLoopProduct
          (((Path.refl ()).map f.continuous).cast rfl rfl)
          (((Path.refl ()).map f.continuous).cast rfl rfl).symm).Homotopy
            (Path.refl ((f ()).trans (f ())))) := by
  let f : C(Unit, Path (0 : ℝ) 0) := ContinuousMap.const _ (Path.refl 0)
  let bump (t : unitInterval) : Path (0 : ℝ) 0 :=
    { toFun s := (t : ℝ) * (1 - t) * s * (1 - s)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hb : Continuous bump := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : unitInterval × unitInterval =>
      (z.1 : ℝ) * (1 - z.1) * z.2 * (1 - z.2))
    fun_prop
  let H : (⟨fun w => (f ()).trans (f w), by fun_prop⟩ :
      C(Unit, Path (0 : ℝ) 0)).Homotopy
      ⟨fun w => (f w).trans (f ()), by fun_prop⟩ :=
    { toFun z := bump z.1
      continuous_toFun := hb.comp continuous_fst
      map_zero_left := by intro w; ext s; simp [bump, f, Path.refl_trans_refl]
      map_one_left := by intro w; ext s; simp [bump, f, Path.refl_trans_refl] }
  refine ⟨H, ?_, ⟨inverseAxisCap f () H (f ()) rfl (Path.refl ())⟩⟩
  change (1 / 2 : ℝ) * (1 - 1 / 2) * (1 / 2) * (1 - 1 / 2) = 1 / 16
  norm_num

-- Every parameter of the constructed row commutation is the genuine categorical braiding.
example (F : Type u) [Field F] (χ : (Fˣ × Fˣ) →* Fˣ)
    (t q : unitInterval) (z : ClassifyingSpace (TorusSource F)) :
    scalarRowLoopCommutation F χ (t, z) q =
      coreLoopCommutation (exactStructure Fᵐᵒᵖ) (constantRow F) (scalarRow F χ) (t, z) q := rfl
