/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.QuillenEquivalence

/-!
# Matsumoto's characteristic-zero equivalences and scalar-extension maps

The forward map is literal, both inverse squares retain the actual K and SmallK
maps, and the negative normalization is the negative of that same inverse.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

variable (F L : Type u) [Field F] [CharZero F] [Field L] [CharZero L]

example : (MilnorKTheory.rightProjectiveKTwoEquivCharZero F).toAddMonoidHom =
    MilnorKTheory.toRightProjectiveKTwo F := rfl

example : (MilnorKTheory.upperModuleKTwoEquivCharZero F).toAddMonoidHom =
    MilnorKTheory.toUpperModuleKTwo F := rfl

example (f : F →+* L)
    (z : Additive ((ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2)) :
    (MilnorKTheory.rightProjectiveKTwoEquivCharZero L).symm
        (((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2).toAdditive z) =
      (milnorKTheoryMap f 2).toAddMonoidHom
        ((MilnorKTheory.rightProjectiveKTwoEquivCharZero F).symm z) :=
  MilnorKTheory.rightProjectiveKTwoEquivCharZero_symm_naturality f z

example (f : F →+* L)
    (z : Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2)) :
    (MilnorKTheory.upperModuleKTwoEquivCharZero L).symm
        (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z) =
      (milnorKTheoryMap f 2).toAddMonoidHom
        ((MilnorKTheory.upperModuleKTwoEquivCharZero F).symm z) :=
  MilnorKTheory.upperModuleKTwoEquivCharZero_symm_naturality f z

example (m : MilnorKTheory F 2) :
    MilnorKTheory.upperModuleKTwoNegativeEquivCharZero F
      (MilnorKTheory.toUpperModuleKTwo F m) = -m :=
  MilnorKTheory.upperModuleKTwoNegativeEquivCharZero_milnor F m

example (a b : Fˣ) :
    MilnorKTheory.upperModuleKTwoEquivCharZero F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct F a b) :=
  MilnorKTheory.upperModuleKTwoEquivCharZero_pair F a b

example (a b : Fˣ) :
    MilnorKTheory.upperModuleKTwoNegativeEquivCharZero F
        (Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct F a b)) =
      -milnorKTupleSymbol ![a, b] :=
  MilnorKTheory.upperModuleKTwoNegativeEquivCharZero_unitProduct F a b

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for decl in #[``StableSteinberg.milnorKernelEquiv,
      ``MilnorKTheory.rightProjectiveKTwoEquivCharZero,
      ``MilnorKTheory.upperModuleKTwoEquivCharZero] do
    unless (Colib.Library.citations env).any (fun citation =>
        citation.declName == decl && citation.source == "Matsumoto1969" &&
        citation.locator == "Section 5, Theorem 5.10 and Corollary 5.11, pp. 30-31" &&
        citation.relation == "adaptation") do
      throwError "Matsumoto's original theorem must be cited on {decl}"
  unless (Colib.Library.citations env).any (fun citation =>
      citation.declName == ``MilnorKTheory.upperModuleKTwoEquivCharZero &&
      citation.source == "WeibelKBook" && citation.locator == "IV, Corollary 1.7.1" &&
      citation.relation == "comparison") do
    throwError "The Quillen K2 model identification must retain its separate reference"
