/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Scheme.VectorBundle.Exact
public import Colib.AlgebraicGeometry.Scheme.Coherent.Exact
public import Colib.KTheory.Quillen.SmallModel.Exact

/-!
# Native scheme K-theory and coherent G-theory

Scheme K-theory uses the existing category `Scheme.Vect` of finite locally free
module sheaves and its ambient short exact sequences. Coherent G-theory uses
the existing abelian category of coherent module sheaves. Both use Mathlib's
actual categorical small model in the explicitly enlarged universe `u + 1`.
No essential-smallness assertion in the smaller universe is required.

Implementation provenance: `Quillen/AlgebraicGeometry/Scheme/VectorBundle/KTheory.lean`,
`Scheme/KTheory.lean`, `Scheme/Coherent/Basic.lean` and `Scheme/GTheory.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native categories
replace the earlier Aglib models; the exact small-model K-construction is unchanged.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

/-- Scheme K-theory of actual finite locally free module sheaves, in the
explicit upper small universe. No noetherian hypothesis is needed. -/
abbrev K (X : Scheme.{u}) (n : ℕ) : Type (u + 1) :=
  ExactStructure.SmallK.{u + 1} (Modules.vectorBundleExactStructure X) n

/-- Coherent G-theory in the explicit upper small universe. -/
abbrev G (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) : Type (u + 1) :=
  ExactStructure.SmallK.{u + 1} (Modules.coherentExactStructure X) n

attribute [colib_tag "COL-0285",
  colib_ref "Quillen1973"
    "Section 7, subsection 1, equation (1.1) and following paragraph, p. 124"
    "adaptation" "Native vector-bundle and coherent K-groups in the explicit upper small universe"]
  K G

end AlgebraicGeometry.Scheme
