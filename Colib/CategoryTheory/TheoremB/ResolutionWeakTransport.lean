/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.ResolutionFiber
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-!
# Canonical weak comparison through the categorical resolution

At the identity comma object the already constructed resolution homotopy
fixes the actual constant-path basepoint. Thus all-degree bijectivity of
the strict resolved comparison transfers to the prescribed original
comparison, including π₀. No based inverse homotopy is assumed.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/ResolutionWeakTransport.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

noncomputable section
open SSet TopCat Topology CategoryTheory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The actual resolution fiber equivalence carries the identity strict
comparison point to the canonical constant-path basepoint. -/
theorem resolutionFiberEquiv_identity (c : C) :
    (resolutionFiberEquiv F (F.obj c)).toFun
      (resolutionStrictFiberComparison F (F.obj c)
        (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c))))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c) :=
  ((resolutionComparisonHomotopy F (F.obj c)).map_zero_left
    (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c))))).symm.trans
      (resolutionComparisonHomotopy_identity F c 0)

/-- A proved weak strict-fiber comparison in the resolution yields the
canonical original comma-to-fiber bijection in every homotopy degree.
This transports actual maps; it does not assert the open finite-stage
cartesian gluing input. -/
theorem fiberComparison_bijective_of_resolutionStrict (c : C) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.map (N := Fin n)
      (resolutionStrictFiberComparison F (F.obj c))
      (x := classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) rfl)) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (fiberComparison F (F.obj c)) (fiberComparison_identity F c)) := by
  have hcomp := homotopyGroupMap_bijective_comp
    (resolutionStrictFiberComparison F (F.obj c)) (resolutionFiberEquiv F (F.obj c)).toFun
    rfl (resolutionFiberEquiv_identity F c) n h
    (homotopyGroupMap_bijective_of_homotopyEquiv
      (resolutionFiberEquiv F (F.obj c)) (resolutionFiberEquiv_identity F c) n)
  exact homotopyGroupMap_bijective_of_based_homotopy
    (f := transferredResolutionComparison F (F.obj c))
    (g := fiberComparison F (F.obj c))
    (x := classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c))))
    (resolutionFiberEquiv_identity F c) (fiberComparison_identity F c)
    (resolutionComparisonHomotopy F (F.obj c))
    (resolutionComparisonHomotopy_identity F c) n hcomp

/-- The positive-degree group isomorphism uses exactly the canonical comma
comparison; the resolution enters only in its proved bijectivity. -/
def fiberComparisonPiEquivOfResolutionStrict (c : C) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.map (N := Fin (n + 1))
      (resolutionStrictFiberComparison F (F.obj c))
      (x := classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) rfl)) :
    HomotopyGroup.Pi (n + 1) (ClassifyingSpace (CostructuredArrow F (F.obj c)))
      (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) ≃*
    HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c)))
      (HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c)) :=
  MulEquiv.ofBijective
    (HomotopyGroup.piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c))
    (fiberComparison_bijective_of_resolutionStrict F c (n + 1) h)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem fiberComparisonPiEquivOfResolutionStrict_coe (c : C) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.map (N := Fin (n + 1))
      (resolutionStrictFiberComparison F (F.obj c))
      (x := classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) rfl)) :
    ↑(fiberComparisonPiEquivOfResolutionStrict F c n h) =
      HomotopyGroup.piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c) := rfl

end CategoryTheory.TheoremB
