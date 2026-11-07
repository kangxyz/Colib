/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.RealizationSkeleton
public import Colib.Topology.Homotopy.Extension
public import Colib.Topology.Realization.MonomorphismHEP

/-! Source: Quillen/CategoryTheory/TheoremA/EnrichedBoundaryHEP.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-!
# Homotopy extension for the actual enriched boundary inclusions

The external-product diagonal is its actual simplicial product. Its boundary
map is a monomorphism, so the existing all-simplicial-monomorphisms realization
HEP theorem applies directly. The diagonal outer-product isomorphism and its
naturality transport this HEP to the actual enriched boundary inclusion.
The native lower theorem already treats the empty zero-dimensional boundary.
-/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

/-- The diagonal of an external product is its ordinary simplicial product. -/
def diagonalOuterProductIso (K X : SSet.{u}) :
    diagonalSSet (outerProduct K X) ≅ X ⊗ K :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso
    { toFun := fun x ↦ (x.2, x.1)
      invFun := fun x ↦ ⟨x.2, x.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (by intros; rfl)

@[reassoc]
theorem diagonalOuterProductIso_naturality {K L X : SSet.{u}} (f : K ⟶ L) :
    diagonalMap (outerProductMap (X := X) f) ≫ (diagonalOuterProductIso L X).hom =
      (diagonalOuterProductIso K X).hom ≫ (X ◁ f) := rfl

/-- Realized product boundary HEP follows from the existing all-simplicial-mono theorem. -/
theorem homotopyExtensionProperty_realizationProductBoundary (X : SSet.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (SSet.toTop.map (X ◁ ∂Δ[n].ι)) := by
  let : Mono (X ◁ ∂Δ[n].ι) := by
    apply (NatTrans.mono_iff_mono_app _).2
    intro k
    apply (mono_iff_injective _).2
    intro a b h
    change (a.1, a.2.val) = (b.1, b.2.val) at h
    have h₁ : a.1 = b.1 := congrArg (fun z => z.1) h
    have h₂ : a.2.val = b.2.val := congrArg (fun z => z.2) h
    exact _root_.Prod.ext h₁ (Subtype.ext h₂)
  exact SSet.homotopyExtensionProperty_realization_mono (X ◁ ∂Δ[n].ι)

/-- The actual enriched boundary map used in replacement skeleta has HEP. -/
theorem homotopyExtensionProperty_enrichedBoundary (X : SSet.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty
      (SSet.toTop.map (diagonalMap (outerProductMap (X := X) ∂Δ[n].ι))) := by
  apply TopCat.homotopyExtensionProperty_of_iso_square _ (SSet.toTop.map (X ◁ ∂Δ[n].ι))
    (SSet.toTop.mapIso (diagonalOuterProductIso (∂Δ[n] : SSet.{u}) X))
    (SSet.toTop.mapIso (diagonalOuterProductIso Δ[n] X))
  · simpa only [Functor.mapIso_hom, ← Functor.map_comp] using
      congrArg SSet.toTop.map (diagonalOuterProductIso_naturality (X := X) ∂Δ[n].ι)
  · exact homotopyExtensionProperty_realizationProductBoundary X n

/-- In particular every single enriched cell boundary in the replacement has HEP. -/
theorem homotopyExtensionProperty_replacementCellBoundary
    {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})
    {n : ℕ} (s : (nerve D).nonDegenerate n) :
    TopCat.HomotopyExtensionProperty (SSet.toTop.map (diagonalMap (replacementCellBoundaryι H s)))
      :=
  homotopyExtensionProperty_enrichedBoundary (H.obj (s.1.obj 0)) n

end CategoryTheory.TheoremA
