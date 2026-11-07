/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.MilnorK.Steinberg.Equivalence
public import Colib.KTheory.Quillen.Field.SteinbergFiberInjectivity
public import Colib.KTheory.MilnorK.QuillenSurjectivity
public import Colib.KTheory.MilnorK.QuillenNaturality
public import Colib.KTheory.Quillen.Field.PositiveSymbolMarking

/-!
# Matsumoto's theorem for Quillen K₂ in characteristic zero

The forward maps are the original right-projective and upper finite-module maps.
Native Matsumoto injectivity, genuine stable-fiber perfectness and the constructed
geometric detector supply bijectivity. Both directions retain the original scalar
extension maps. The negative normalization is minus the same positive inverse.

The mathematical attribution is Matsumoto (1969), Section 5, Theorem 5.10 and
Corollary 5.11, pp. 30–31, specialized to stable type A over characteristic-zero
fields. Weibel, III, Theorem 6.1 gives the familiar K₂ formulation. The separate
identification with homotopy-defined K₂ is described in Weibel, IV, Corollary 1.7.1.
The original paper does not define Quillen's later K-groups, and the general
Milnor-to-Quillen comparison in other degrees is not Matsumoto's theorem.

Implementation source: `Quillen/KTheory/Field/MilnorKTwoEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The ordered positive symbol is
the original scalar identity-action unit product; its negative normalization is
the negative ordered Milnor symbol. No positive-characteristic equivalence is asserted.
-/
@[expose] public section

noncomputable section

universe u

namespace MilnorKTheory

open ModuleCat.FiniteProjective.StableCompletion
open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] StableSteinberg.kernelCommGroup Abelian.hasFiniteBiproducts

variable (F : Type u) [Field F] [CharZero F]

/-- Injectivity of the original kernel map and the original kernel-to-K2 map
imply injectivity of their original right-projective composite. -/
theorem toRightProjectiveKTwo_injective_charZero :
    Function.Injective (toRightProjectiveKTwo F) := by
  intro x y h
  apply StableSteinberg.milnorToKernel_injective_charZero F
  apply Additive.toMul.injective
  apply steinbergKernelToRightProjectiveKTwo_injective F
  exact congrArg Additive.toMul h

/-- The original upper-model composite is injective in characteristic zero. -/
theorem toUpperModuleKTwo_injective_charZero :
    Function.Injective (toUpperModuleKTwo F) := by
  intro x y h
  apply toRightProjectiveKTwo_injective_charZero F
  apply Additive.toMul.injective
  apply (FGModuleCat.rightProjectiveUpperModuleKEquiv F 2).injective
  exact congrArg Additive.toMul h

/-- The original right-projective map is bijective without any fiber-perfectness
or generation premise: the existing theorems supply both. -/
theorem toRightProjectiveKTwo_bijective_charZero :
    Function.Bijective (toRightProjectiveKTwo F) := by
  exact ⟨toRightProjectiveKTwo_injective_charZero F,
    toRightProjectiveKTwo_surjective F⟩

/-- The original upper finite-module map is bijective in characteristic zero. -/
theorem toUpperModuleKTwo_bijective_charZero :
    Function.Bijective (toUpperModuleKTwo F) := by
  exact ⟨toUpperModuleKTwo_injective_charZero F,
    toUpperModuleKTwo_surjective F⟩

/-- Matsumoto's theorem in characteristic zero, with the original right-projective
Quillen K₂ map as its forward homomorphism. -/
def rightProjectiveKTwoEquivCharZero : MilnorKTheory F 2 ≃+
    Additive ((ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2) :=
  AddEquiv.ofBijective (toRightProjectiveKTwo F)
    (toRightProjectiveKTwo_bijective_charZero F)

/-- Matsumoto's theorem in characteristic zero for upper finite-module Quillen K₂,
with the original forward homomorphism. -/
def upperModuleKTwoEquivCharZero : MilnorKTheory F 2 ≃+
    Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2) :=
  AddEquiv.ofBijective (toUpperModuleKTwo F)
    (toUpperModuleKTwo_bijective_charZero F)

/-- The right-projective equivalence retains the literal original homomorphism. -/
theorem rightProjectiveKTwoEquivCharZero_toAddMonoidHom :
    (rightProjectiveKTwoEquivCharZero F).toAddMonoidHom =
      toRightProjectiveKTwo F := rfl

/-- The upper-model equivalence retains the literal original homomorphism. -/
theorem upperModuleKTwoEquivCharZero_toAddMonoidHom :
    (upperModuleKTwoEquivCharZero F).toAddMonoidHom =
      toUpperModuleKTwo F := rfl

/-- Applying the positive right-projective equivalence uses the original map. -/
@[simp] theorem rightProjectiveKTwoEquivCharZero_apply (m : MilnorKTheory F 2) :
    rightProjectiveKTwoEquivCharZero F m = toRightProjectiveKTwo F m := rfl

/-- Applying the positive upper-model equivalence uses the original map. -/
@[simp] theorem upperModuleKTwoEquivCharZero_apply (m : MilnorKTheory F 2) :
    upperModuleKTwoEquivCharZero F m = toUpperModuleKTwo F m := rfl

/-- The ordered right-projective symbol retains the original ordered kernel defect. -/
theorem rightProjectiveKTwoEquivCharZero_pair (a b : Fˣ) :
    rightProjectiveKTwoEquivCharZero F (milnorKTupleSymbol ![a, b]) = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) :=
  toRightProjectiveKTwo_pair F a b

/-- The ordered upper-model symbol is the original positive scalar unit product. -/
theorem upperModuleKTwoEquivCharZero_pair (a b : Fˣ) :
    upperModuleKTwoEquivCharZero F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct F a b) :=
  toUpperModuleKTwo_pair_eq_unitProduct F a b

variable {F} {L : Type u} [Field L] [CharZero L] (f : F →+* L)

/-- The positive right-projective equivalence commutes with original scalar extension. -/
theorem rightProjectiveKTwoEquivCharZero_naturality (m : MilnorKTheory F 2) :
    ((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2).toAdditive
        (rightProjectiveKTwoEquivCharZero F m) =
      rightProjectiveKTwoEquivCharZero L ((milnorKTheoryMap f 2).toAddMonoidHom m) :=
  toRightProjectiveKTwo_naturality f m

/-- The positive upper-model equivalence commutes with literal tensor extension. -/
theorem upperModuleKTwoEquivCharZero_naturality (m : MilnorKTheory F 2) :
    ((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive
        (upperModuleKTwoEquivCharZero F m) =
      upperModuleKTwoEquivCharZero L ((milnorKTheoryMap f 2).toAddMonoidHom m) :=
  toUpperModuleKTwo_naturality f m

/-- The inverse right-projective equivalence is natural for the original K-map. -/
theorem rightProjectiveKTwoEquivCharZero_symm_naturality
    (z : Additive ((ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2)) :
    (rightProjectiveKTwoEquivCharZero L).symm
        (((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2).toAdditive z) =
      (milnorKTheoryMap f 2).toAddMonoidHom ((rightProjectiveKTwoEquivCharZero F).symm z) := by
  have h := rightProjectiveKTwoEquivCharZero_naturality f
    ((rightProjectiveKTwoEquivCharZero F).symm z)
  rw [(rightProjectiveKTwoEquivCharZero F).apply_symm_apply] at h
  exact (congrArg (rightProjectiveKTwoEquivCharZero L).symm h).trans
    ((rightProjectiveKTwoEquivCharZero L).symm_apply_apply _)

/-- The inverse upper-model equivalence is natural for original tensor extension. -/
theorem upperModuleKTwoEquivCharZero_symm_naturality
    (z : Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2)) :
    (upperModuleKTwoEquivCharZero L).symm
        (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z) =
      (milnorKTheoryMap f 2).toAddMonoidHom ((upperModuleKTwoEquivCharZero F).symm z) := by
  have h := upperModuleKTwoEquivCharZero_naturality f
    ((upperModuleKTwoEquivCharZero F).symm z)
  rw [(upperModuleKTwoEquivCharZero F).apply_symm_apply] at h
  exact (congrArg (upperModuleKTwoEquivCharZero L).symm h).trans
    ((upperModuleKTwoEquivCharZero L).symm_apply_apply _)

variable (F)

/-- The explicitly NEGATIVE inverse of the positive upper-model equivalence. -/
def upperModuleKTwoNegativeEquivCharZero :
    Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2) ≃+
      MilnorKTheory F 2 :=
  (upperModuleKTwoEquivCharZero F).symm.trans (AddEquiv.neg _)

/-- The negative normalization is literally minus the positive inverse. -/
@[simp] theorem upperModuleKTwoNegativeEquivCharZero_apply
    (z : Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2)) :
    upperModuleKTwoNegativeEquivCharZero F z =
      -((upperModuleKTwoEquivCharZero F).symm z) := rfl

/-- Normalizing the original forward Milnor map gives the negative input. -/
theorem upperModuleKTwoNegativeEquivCharZero_milnor (m : MilnorKTheory F 2) :
    upperModuleKTwoNegativeEquivCharZero F (toUpperModuleKTwo F m) = -m := by
  change -((upperModuleKTwoEquivCharZero F).symm
    (upperModuleKTwoEquivCharZero F m)) = -m
  rw [(upperModuleKTwoEquivCharZero F).symm_apply_apply]

/-- The original forward map of a negatively normalized class is the negative class. -/
theorem toUpperModuleKTwo_negativeEquivCharZero
    (z : Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2)) :
    toUpperModuleKTwo F (upperModuleKTwoNegativeEquivCharZero F z) = -z := by
  change upperModuleKTwoEquivCharZero F
    (-((upperModuleKTwoEquivCharZero F).symm z)) = -z
  rw [map_neg, (upperModuleKTwoEquivCharZero F).apply_symm_apply]

/-- The inverse negative normalization is minus the SAME original forward map. -/
theorem upperModuleKTwoNegativeEquivCharZero_symm_apply (m : MilnorKTheory F 2) :
    (upperModuleKTwoNegativeEquivCharZero F).symm m =
      -(toUpperModuleKTwo F m) := by
  apply (upperModuleKTwoNegativeEquivCharZero F).injective
  rw [(upperModuleKTwoNegativeEquivCharZero F).apply_symm_apply, map_neg,
    upperModuleKTwoNegativeEquivCharZero_milnor, neg_neg]

/-- The actual positive ordered product normalizes to the negative ordered symbol. -/
theorem upperModuleKTwoNegativeEquivCharZero_unitProduct (a b : Fˣ) :
    upperModuleKTwoNegativeEquivCharZero F
        (Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct F a b)) =
      -milnorKTupleSymbol ![a, b] := by
  rw [← toUpperModuleKTwo_pair_eq_unitProduct F a b,
    upperModuleKTwoNegativeEquivCharZero_milnor]

variable {F}

/-- The negative normalization commutes with the original upper-model field map. -/
theorem upperModuleKTwoNegativeEquivCharZero_naturality
    (z : Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2)) :
    upperModuleKTwoNegativeEquivCharZero L
        (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z) =
      (milnorKTheoryMap f 2).toAddMonoidHom (upperModuleKTwoNegativeEquivCharZero F z) := by
  change -((upperModuleKTwoEquivCharZero L).symm
    (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z)) =
      (milnorKTheoryMap f 2).toAddMonoidHom (-((upperModuleKTwoEquivCharZero F).symm z))
  rw [upperModuleKTwoEquivCharZero_symm_naturality, map_neg]

/-- Homomorphism form of the negative normalization's original field-map square. -/
theorem upperModuleKTwoNegativeEquivCharZero_naturality_hom :
    (upperModuleKTwoNegativeEquivCharZero L).toAddMonoidHom.comp
        (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive) =
      ((milnorKTheoryMap f 2).toAddMonoidHom).comp
        (upperModuleKTwoNegativeEquivCharZero F).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro z
  exact upperModuleKTwoNegativeEquivCharZero_naturality f z

/-- The inverse negative normalization also commutes with the original field maps. -/
theorem upperModuleKTwoNegativeEquivCharZero_symm_naturality (m : MilnorKTheory F 2) :
    ((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive
        ((upperModuleKTwoNegativeEquivCharZero F).symm m) =
      (upperModuleKTwoNegativeEquivCharZero L).symm ((milnorKTheoryMap f 2).toAddMonoidHom m) := by
  rw [upperModuleKTwoNegativeEquivCharZero_symm_apply,
    upperModuleKTwoNegativeEquivCharZero_symm_apply, map_neg,
    toUpperModuleKTwo_naturality]

end MilnorKTheory

namespace MilnorKTheory

attribute [colib_ref "Matsumoto1969" "Section 5, Theorem 5.10 and Corollary 5.11, pp. 30-31"
    "adaptation" "Stable type A specialization over characteristic-zero fields, followed by \
      the separate identification with Quillen K2",
  colib_ref "WeibelKBook" "III, Theorem 6.1" "adaptation"
    "Matsumoto's field K2 presentation, restricted here to characteristic zero",
  colib_ref "WeibelKBook" "IV, Corollary 1.7.1" "comparison"
    "Identification of classical Steinberg-kernel K2 with homotopy-defined K2, realized here \
      in the existing exact-category models"]
  rightProjectiveKTwoEquivCharZero upperModuleKTwoEquivCharZero

attribute [colib_tag "COL-0262",
  colib_ref "quillen" "Quillen/KTheory/Field/MilnorKTwoEquivalence.lean, lines 73-226"
    "adaptation" "Characteristic-zero maps, ordered product and both field-change squares"]
  rightProjectiveKTwoEquivCharZero upperModuleKTwoEquivCharZero
  rightProjectiveKTwoEquivCharZero_toAddMonoidHom upperModuleKTwoEquivCharZero_toAddMonoidHom
  rightProjectiveKTwoEquivCharZero_naturality upperModuleKTwoEquivCharZero_naturality
  rightProjectiveKTwoEquivCharZero_symm_naturality upperModuleKTwoEquivCharZero_symm_naturality
  upperModuleKTwoEquivCharZero_pair upperModuleKTwoNegativeEquivCharZero
  upperModuleKTwoNegativeEquivCharZero_apply upperModuleKTwoNegativeEquivCharZero_unitProduct
  upperModuleKTwoNegativeEquivCharZero_naturality
  upperModuleKTwoNegativeEquivCharZero_symm_naturality

end MilnorKTheory
