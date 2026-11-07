/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Scheme.Comparison
public import Colib.AlgebraicGeometry.KTheory.Restriction
public import Colib.KTheory.Quillen.SmallModel.Functoriality

/-!
# The canonical comparison from native scheme K-theory to G-theory

Finite locally free sheaves on a locally noetherian scheme are coherent. Their
actual exact inclusion induces the canonical K-to-G homomorphism. The literal
geometric restriction square induces a strict equality of group homomorphisms.

Implementation provenance: `Quillen/AlgebraicGeometry/Scheme/Comparison/KToG.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The underlying
exact inclusion and its canonical small-model K-map are retained.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

/-- The canonical comparison induced by the actual exact inclusion. -/
def KToG (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) : K X n →* G X n :=
  (Modules.vectorBundleToCoherentExact X).smallKMap n

@[simp]
theorem KToG_eq_smallKMap (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    KToG X n = (Modules.vectorBundleToCoherentExact X).smallKMap n := rfl

/-- The canonical comparison commutes with actual open restriction. -/
theorem KToG_restrict {U X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian U] (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (restrictG j n).comp (KToG X n) = (KToG U n).comp (restrictK j n) := by
  change ((Modules.coherentRestrictionExact j).smallKMap n).comp
      ((Modules.vectorBundleToCoherentExact X).smallKMap n) =
    ((Modules.vectorBundleToCoherentExact U).smallKMap n).comp
      ((Modules.vectorBundleExactRestrict j).smallKMap n)
  rw [← ExactFunctor.smallKMap_comp, ← ExactFunctor.smallKMap_comp]
  exact ExactFunctor.smallKMap_eq_of_natIso
    (Modules.vectorBundleToCoherentRestrictIso j) n

/-- Elementwise naturality of the canonical comparison. -/
theorem KToG_restrict_apply {U X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian U] (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (x : K X n) :
    restrictG j n (KToG X n x) = KToG U n (restrictK j n x) :=
  DFunLike.congr_fun (KToG_restrict j n) x

attribute [colib_tag "COL-0285",
  colib_ref "Quillen1973"
    "Section 7, subsection 1, equation (1.1) and following paragraph, p. 124"
    "adaptation" "The canonical connective inclusion map, natural for actual open restriction"]
  KToG KToG_restrict

end AlgebraicGeometry.Scheme
