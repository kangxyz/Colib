/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FilteredHomology
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
Adapted from `Quillen/Topology/LocalCoefficients/FilteredHomologyElements.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the native singular
chain complex, actual transition maps, and coefficient transports.

# Finite-stage representatives and detection of zero in actual local homology

These are elementwise consequences of the proved chain-colimit comparison,
with precisely the original stage pushforward maps. No stage injectivity or
homological stability assumption is made.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : ℕ)

private theorem forget_preserves :
    PreservesColimitsOfShape J (forget (ModuleCat.{u} ℤ)) := by
  change PreservesColimitsOfShape J
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat ⋙ forget AddCommGrpCat)
  infer_instance

include hc

/-- Every class in the actual target homology comes from one actual finite stage. -/
theorem filteredHomology_exists_stage (x : homology A n) :
    ∃ (j : J) (y : (filteredHomologyDiagram F c A n).obj j),
      pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n y = x := by
  let := forget_preserves (J := J)
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (ModuleCat.{u} ℤ))
      (filteredHomologyIsColimit F c hc A n)) x

/-- Equality of classes from the same stage is detected after one transition. -/
theorem filteredHomology_eq_iff {j : J}
    (x y : (filteredHomologyDiagram F c A n).obj j) :
    pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n x =
        pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n y ↔
      ∃ (k : J) (f : j ⟶ k),
        (filteredHomologyDiagram F c A n).map f x =
          (filteredHomologyDiagram F c A n).map f y := by
  let := forget_preserves (J := J)
  exact Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget (ModuleCat.{u} ℤ))
      (filteredHomologyIsColimit F c hc A n)) x y

/-- A class vanishes in the target precisely when it vanishes at a later stage. -/
theorem filteredHomology_eq_zero_iff {j : J}
    (x : (filteredHomologyDiagram F c A n).obj j) :
    pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n x = 0 ↔
      ∃ (k : J) (f : j ⟶ k), (filteredHomologyDiagram F c A n).map f x = 0 := by
  have hzero : pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n 0 = 0 :=
    (pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n).hom.map_zero
  have h := filteredHomology_eq_iff F c hc A n x 0
  rw [hzero] at h
  simpa using h

end FundamentalGroupoid.LocalCoefficients
