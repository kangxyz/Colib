/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Localization.Serre.BasedFiberComparison
public import Colib.Topology.HomotopyFiber.LES

/-!
# The actual path-space boundary of the Serre quotient

The normalized quotient map defines a concrete path-space homotopy fiber.
Its connecting homomorphism is the native topological boundary, with the
original quotient K-map and original fiber projection at every exactness
position. Its target is the fiber's homotopy group, not K-theory of the Serre
subcategory. The later `FiberEquivalence` module supplies their canonical
identification. That geometric result is not assumed in this lower leaf.

The construction is adapted from the unconditional path-space portions of
`Quillen/Localization/Serre/LocalizationLESAdapter.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native path-space LES theorems are
used directly; no conditional comparison package is introduced.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian

variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The genuine path-space boundary of the actual normalized quotient map. -/
def fiberConnectingHom (n : ℕ) :
    (abelianExactStructure P.isoModSerre.Localization).K (n + 1) →*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P) :=
  HomotopyFiber.connectingHom
    (classifyingSpaceMap (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ).hom
    (abelianExactStructure P.isoModSerre.Localization).kBasepoint
    (abelianExactStructure C).kBasepoint
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ_map_point n

/-- Exactness at the quotient term, with the actual boundary into the path-space fiber. -/
theorem quotient_range_eq_fiberConnecting_ker (n : ℕ) :
    (quotientKMap P (n + 1)).range = (fiberConnectingHom P n).ker :=
  HomotopyFiber.range_piMap_eq_ker_connectingHom _ _ _ _ n

/-- Exactness at the concrete fiber's homotopy group, before any Serre comparison. -/
theorem fiberConnecting_range_eq_projection_ker (n : ℕ) :
    (fiberConnectingHom P n).range = (localizationFiberProjectionHom P n).ker :=
  HomotopyFiber.range_connectingHom_eq_ker_projection _ _ _ _ n

/-- The actual path-space projection has image exactly the kernel of the quotient K-map. -/
theorem fiberProjection_range_eq_quotient_ker (n : ℕ) :
    (localizationFiberProjectionHom P n).range = (quotientKMap P n).ker :=
  HomotopyFiber.piMap_range_projection_eq_ker _ _ _ _ n

/-- The genuine comparison carries the Serre inclusion image into the quotient kernel. -/
theorem inclusion_range_le_quotient_ker (n : ℕ) :
    (Abelian.Devissage.KMap P n).range ≤ (quotientKMap P n).ker := by
  rw [← localizationFiberComparisonHom_projection P n,
    ← fiberProjection_range_eq_quotient_ker P n]
  rintro a ⟨b, rfl⟩
  exact ⟨localizationFiberComparisonHom P n b, rfl⟩

end CategoryTheory.ExactCategory.SerreLocalization

attribute [colib_ref "WeibelKBook" "IV, Homotopy Fiber 1.2, page 3" "background"
  "Path-space LES with paths from f(x) to the target basepoint, before Serre identification"]
  CategoryTheory.ExactCategory.SerreLocalization.fiberConnectingHom
  CategoryTheory.ExactCategory.SerreLocalization.quotient_range_eq_fiberConnecting_ker
  CategoryTheory.ExactCategory.SerreLocalization.fiberConnecting_range_eq_projection_ker
  CategoryTheory.ExactCategory.SerreLocalization.fiberProjection_range_eq_quotient_ker
