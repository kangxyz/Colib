/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.KTheory.Quillen.Basic
import Colib.KTheory.Quillen.Map.Basic
import Colib.KTheory.Quillen.Map.Functoriality
import Colib.KTheory.GrothendieckComparison.Injectivity
import Colib.CategoryTheory.TheoremA.ContractibleComma
import Colib.CategoryTheory.TheoremB.WeakComparison
import Colib.KTheory.Quillen.Resolution.LengthOneK
import Colib.KTheory.Quillen.Resolution.Theorem
import Colib.KTheory.Quillen.Devissage.Theorem
import Colib.KTheory.Quillen.Localization.Serre.FiberEquivalence
import Colib.KTheory.Quillen.Localization.Serre.LocalizationTheorem
import Colib.KTheory.Waldhausen.Additivity.Basic
import Colib.KTheory.Waldhausen.Additivity.GroupFormula
import Colib.KTheory.Waldhausen.Additivity.RealizedAdditivity
import Colib.KTheory.Waldhausen.GilletWaldhausen.GeneralComparison

/-! # Original sources for classical categorical and K-theoretic comparisons -/

open Lean Elab Command in
run_cmd do
  let citations := Colib.Library.citations (← getEnv)
  let endpoints : List (Name × String × String) := [
    (``CategoryTheory.ExactCategory.ExactStructure.K,
      "Quillen1973", "Section 2, definition (5), p. 103"),
    (``CategoryTheory.ExactCategory.ExactFunctor.KMap,
      "Quillen1973", "Section 2, equation (6) and following paragraph, p. 103"),
    (``CategoryTheory.ExactCategory.ExactFunctor.KMap_comp,
      "Quillen1973", "Section 2, equation (6) and following paragraph, p. 103"),
    (``CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_bijective,
      "Quillen1973", "Section 2, Theorem 1 and proof, pp. 102-103"),
    (``CategoryTheory.TheoremA.contractibleCommaClassifyingHomotopyEquiv,
      "Quillen1973", "Section 1, Theorem A and its dual formulation, p. 93"),
    (``CategoryTheory.TheoremB.fiberComparison_bijective,
      "Quillen1973", "Section 1, Theorem B and its dual formulation, p. 97"),
    (``CategoryTheory.ExactCategory.Resolution.KEquivOfLengthOne,
      "Quillen1973", "Section 4, Theorem 3 and proof, pp. 108-109"),
    (``CategoryTheory.ExactCategory.Resolution.classifyingHomotopyEquiv,
      "Quillen1973", "Section 4, Corollary 1 and proof, pp. 109-110"),
    (``CategoryTheory.Abelian.Devissage.classifyingHomotopyEquiv,
      "Quillen1973", "Section 5, Theorem 4, p. 112"),
    (``CategoryTheory.ExactCategory.SerreLocalization.localizationFiberEquiv,
      "Quillen1973", "Section 5, Theorem 5 and proof, pp. 113-116"),
    (``CategoryTheory.ExactCategory.SerreLocalization.localizationSequence,
      "Quillen1973", "Section 5, Theorem 5, p. 113"),
    (``CategoryTheory.Waldhausen.Additivity.KMap_additivity,
      "Waldhausen1985", "Proposition 1.3.2(4), pp. 331-332, and Theorem 1.4.2, p. 336"),
    (``CategoryTheory.Waldhausen.Additivity.KMap_additivity_mul,
      "Waldhausen1985", "Proposition 1.3.2(4), pp. 331-332, and Theorem 1.4.2, p. 336"),
    (``CategoryTheory.Waldhausen.Additivity.deloopingMap_additivity,
      "Waldhausen1985", "Proposition 1.3.2(4), pp. 331-332, and Theorem 1.4.2, p. 336"),
    (``CategoryTheory.Waldhausen.GilletWaldhausen.boundedTermsSingle_coarse_KMap_bijective_general,
      "ThomasonTrobaugh1990", "Theorem 1.11.7, pp. 279-281, with Section 1.11.3.1, p. 278")]
  for (decl, source, locator) in endpoints do
    unless citations.any (fun citation => citation.declName == decl &&
        citation.source == source && citation.locator == locator) do
      throwError "Missing original mathematical source for {decl}"
    unless citations.any (fun citation => citation.declName == decl &&
        citation.source == "WeibelKBook") do
      throwError "Missing retained modern reference for {decl}"
