/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.KTheory.Waldhausen.QuillenComparison.Equivalence
import Colib.KTheory.Waldhausen.ExactEquivalence
import Colib.KTheory.Quillen.FiniteSupport.Decomposition

/-! # Mathematical attribution and independent implementation provenance -/

open Lean Elab Command in
run_cmd do
  let citations := Colib.Library.citations (← getEnv)
  let endpoints : List (Name × String × String × String) := [
    (``CategoryTheory.Waldhausen.QuillenComparison.comparisonKEquiv,
      "Waldhausen1985", "Section 1.9, pp. 375-376", "adaptation"),
    (``CategoryTheory.Waldhausen.KEquivOfExactEquivalence,
      "Waldhausen1985", "Section 1.3, Proposition 1.3.1, pp. 330-331", "ingredient"),
    (``CategoryTheory.Pi.FiniteSupport.decompositionKEquiv,
      "Quillen1973", "Section 2, equations (8)-(9), pp. 103-104", "ingredient")]
  for (decl, source, locator, relation) in endpoints do
    unless citations.any (fun citation => citation.declName == decl &&
        citation.source == source && citation.locator == locator &&
        citation.relation == relation) do
      throwError "Missing precise mathematical reference for {decl}"
    unless citations.any (fun citation => citation.declName == decl &&
        citation.source == "quillen") do
      throwError "Missing implementation provenance for {decl}"
