/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Quillen.Field.FiniteFieldKTwo
import Mathlib.Algebra.Field.ZMod

/-!
# Finite-field K₂, including the two smallest fields

Regressions retain the actual native Milnor group, original right-projective
Quillen target and original upper finite-module SmallK universe.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable (F : Type u) [Field F] [Finite F]

example (z : MilnorKTheory F 2) : z = 0 := MilnorKTheory.eq_zero_of_finite z

example : Subsingleton (MilnorKTheory F 2) := inferInstance

example (a : (ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2) : a = 1 :=
  Quillen.Field.rightProjectiveKTwo_eq_one F a

example (a : (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2) : a = 1 :=
  Quillen.Field.upperModuleKTwo_eq_one F a

example : Subsingleton (MilnorKTheory (ZMod 2) 2) := inferInstance

example : Subsingleton (MilnorKTheory (ZMod 3) 2) := inferInstance

example : Subsingleton
    ((ModuleCat.FiniteProjective.exactStructure.{0, 0} (ZMod 2)ᵐᵒᵖ).K 2) :=
  Quillen.Field.rightProjectiveKTwo_subsingleton (ZMod 2)

example : Subsingleton
    ((ModuleCat.FiniteProjective.exactStructure.{0, 0} (ZMod 3)ᵐᵒᵖ).K 2) :=
  Quillen.Field.rightProjectiveKTwo_subsingleton (ZMod 3)

example : Subsingleton ((abelianExactStructure (FGModuleCat.{0} (ZMod 2))).SmallK.{1} 2) :=
  Quillen.Field.upperModuleKTwo_subsingleton (ZMod 2)

example : Subsingleton ((abelianExactStructure (FGModuleCat.{0} (ZMod 3))).SmallK.{1} 2) :=
  Quillen.Field.upperModuleKTwo_subsingleton (ZMod 3)

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless (Colib.Library.citations env).any (fun citation =>
      citation.declName == ``MilnorKTheory.eq_zero_of_finite &&
      citation.source == "Milnor1970" &&
      citation.locator == "Section 1, Example 1.5 (Steinberg), p. 321" &&
      citation.relation == "clause") do
    throwError "Finite-field Milnor K2 must retain Steinberg's attribution in Milnor's paper"
  unless (Colib.Library.citations env).any (fun citation =>
      citation.declName == ``Quillen.Field.upperModuleKTwo_eq_one &&
      citation.source == "WeibelKBook" && citation.locator == "IV, Corollary 1.7.1" &&
      citation.relation == "comparison") do
    throwError "The finite-field Quillen target must retain its separate model comparison"
