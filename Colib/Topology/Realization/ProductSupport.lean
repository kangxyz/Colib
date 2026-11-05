/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.FiniteCompact

/-! # Compact support in one finite factor of a simplicial product

A compact-source map into the realization of `X × Y` has an exact lift to
`X × B` for one genuinely finite subcomplex `B` of `Y`. The finite range of
the second projection of its finite support supplies this single common factor.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u

namespace SSet.ProductRealization
variable {A X Y : SSet.{u}}

/-- The actual simplicial range of a map's second component. -/
def rightRange (f : A ⟶ X ⊗ Y) : Y.Subcomplex :=
  SSet.Subcomplex.range (f ≫ snd X Y)

/-- The exact factor through that right-hand range. -/
def factorRight (f : A ⟶ X ⊗ Y) : A ⟶ X ⊗ (rightRange f : SSet.{u}) :=
  lift (f ≫ fst X Y) (SSet.Subcomplex.toRange (f ≫ snd X Y))

/-- The actual product inclusion recovers precisely the original simplicial map. -/
@[reassoc (attr := simp)] theorem factorRight_inclusion (f : A ⟶ X ⊗ Y) :
    factorRight f ≫ X ◁ (rightRange f).ι = f := by
  ext n a <;> rfl

/-- A genuinely finite source gives a genuinely finite right-hand range. -/
instance rightRange_finite (f : A ⟶ X ⊗ Y) [A.Finite] : SSet.Finite (rightRange f) :=
  inferInstanceAs (SSet.Finite (SSet.Subcomplex.range (f ≫ snd X Y)))

/-- Exact compact-source factorization through one finite right subcomplex.
In particular, one compact finite family of points uses one common factor. -/
theorem compact_right_factors {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, |X ⊗ Y|)) :
    ∃ B : Y.Subcomplex, SSet.Finite B ∧ ∃ g : C(T, |X ⊗ (B : SSet.{u})|),
      (SSet.toTop.map (X ◁ B.ι)).hom.comp g = f := by
  obtain ⟨A, hA, g, hg⟩ := realization_continuousMap_factors_finiteSubcomplex f
  let : SSet.Finite (A : SSet.{u}) := hA
  refine ⟨rightRange A.ι, inferInstance, (SSet.toTop.map (factorRight A.ι)).hom.comp g, ?_⟩
  change (SSet.toTop.map (factorRight A.ι) ≫
    SSet.toTop.map (X ◁ (rightRange A.ι).ι)).hom.comp g = f
  rw [← CategoryTheory.Functor.map_comp, factorRight_inclusion]
  exact hg

/-- Two actual points are simultaneously represented over one finite right
subcomplex; this is the common-stage input needed for product injectivity. -/
theorem pair_right_factors (p q : |X ⊗ Y|) :
    ∃ B : Y.Subcomplex, SSet.Finite B ∧
      ∃ p' q' : |X ⊗ (B : SSet.{u})|,
        SSet.toTop.map (X ◁ B.ι) p' = p ∧ SSet.toTop.map (X ◁ B.ι) q' = q := by
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := ⟨rfl⟩
  let f : C(Bool, |X ⊗ Y|) := ⟨fun b ↦ if b = true then p else q, continuous_of_discreteTopology⟩
  obtain ⟨B, hB, g, hg⟩ := compact_right_factors f
  exact ⟨B, hB, g true, g false, DFunLike.congr_fun hg true, DFunLike.congr_fun hg false⟩

end SSet.ProductRealization
