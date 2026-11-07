/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.MilnorK.FiniteField
public import Colib.KTheory.MilnorK.QuillenSurjectivity

/-!
# Quillen K₂ of finite fields

The canonical native Milnor-to-Quillen maps are surjective over every field.
Native integral Milnor K₂ vanishing therefore makes the original right-projective
K₂ and the upper `SmallK.{u+1}` of `FGModuleCat.{u} F` trivial. No replacement
group, characteristic restriction, or external perfectness premise is used.

The vanishing is the K₂ case of the classical finite-field calculation, not a
computation of all higher Quillen K-groups. Milnor (1970), Section 1, Example 1.5
attributes the symbol calculation to Steinberg; see also Weibel, III,
Corollary 6.1.1. The identification of classical K₂ with homotopy-defined K₂
is separate (Weibel, IV, Corollary 1.7.1). This proof uses all-field surjectivity,
not the characteristic-zero Matsumoto equivalences.

Implementation provenance: this adapts the right-projective and upper finite-module clauses of
`Quillen/KTheory/Field/FiniteFieldKTwo.lean` at revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Lower-universe G₂ and coherent
scheme G₂ comparisons are separate consumers of these original targets.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Field

variable (F : Type u) [Field F] [Finite F]

/-- Every class in the original right-projective K₂ group of a finite field is neutral. -/
theorem rightProjectiveKTwo_eq_one
    (a : (ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2) : a = 1 := by
  obtain ⟨z, hz⟩ := MilnorKTheory.toRightProjectiveKTwo_surjective F (Additive.ofMul a)
  rw [MilnorKTheory.eq_zero_of_finite z, map_zero] at hz
  exact congrArg Additive.toMul hz.symm

/-- The original right-projective Quillen K₂ group of every finite field has one element. -/
theorem rightProjectiveKTwo_subsingleton :
    Subsingleton ((ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2) :=
  ⟨fun a b => (rightProjectiveKTwo_eq_one F a).trans (rightProjectiveKTwo_eq_one F b).symm⟩

/-- Every class in the actual upper finite-module K₂ group of a finite field is neutral. -/
theorem upperModuleKTwo_eq_one
    (a : (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2) : a = 1 := by
  obtain ⟨z, hz⟩ := MilnorKTheory.toUpperModuleKTwo_surjective F (Additive.ofMul a)
  rw [MilnorKTheory.eq_zero_of_finite z, map_zero] at hz
  exact congrArg Additive.toMul hz.symm

/-- The original upper finite-module Quillen K₂ group of every finite field has one element. -/
theorem upperModuleKTwo_subsingleton :
    Subsingleton ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2) :=
  ⟨fun a b => (upperModuleKTwo_eq_one F a).trans (upperModuleKTwo_eq_one F b).symm⟩

attribute [colib_tag "COL-0280",
  colib_ref "Milnor1970" "Section 1, Example 1.5 (Steinberg), p. 321" "ingredient"
    "Integral Milnor K2 vanishing, passed through the original surjective comparison maps",
  colib_ref "WeibelKBook" "III, Corollary 6.1.1" "adaptation"
    "Finite-field K2 vanishing on the existing right-projective and upper finite-module groups",
  colib_ref "WeibelKBook" "IV, Corollary 1.7.1" "comparison"
    "The separate identification of classical K2 with homotopy-defined K2",
  colib_ref "quillen"
  "Quillen/KTheory/Field/FiniteFieldKTwo.lean, rightProjectiveKTwo and upperModuleKTwo clauses"
  "adaptation" "Original right-projective K2 and upper FGModuleCat SmallK2, for every finite field"]
  rightProjectiveKTwo_eq_one rightProjectiveKTwo_subsingleton
  upperModuleKTwo_eq_one upperModuleKTwo_subsingleton

end Quillen.Field
