/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References

public import Colib.Topology.Realization.FiniteHausdorff
public import Colib.Topology.Realization.LocallyCompactProduct
public import Colib.Topology.Realization.ProductSupport
public import Colib.Topology.Homotopy.HomotopyGroup.CompactLifting
public import Colib.Topology.Homotopy.HomotopyGroup.Product

/-! # The actual realization-product map on based homotopy groups

Finite right support gives injectivity of the canonical comparison and exact
continuous lifting of all compact-source maps. This proves its actual based
homotopy-group bijectivity without asserting a homeomorphism for arbitrary
ordinary topological products.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u

namespace SSet.ProductRealization

/-- The original canonical realization-product comparison. -/
def comparison (X Y : SSet.{u}) : C(|X ⊗ Y|, |X| × |Y|) :=
  (prodComparison SSet.toTop X Y).hom

/-- With a genuinely finite right factor the original comparison is a homeomorphism. -/
def finiteRightHomeomorph (X Y : SSet.{u}) [Y.Finite] : |X ⊗ Y| ≃ₜ |X| × |Y| := by
  letI := realizationProductComparison_isIso_of_locallyCompact X Y
  exact TopCat.homeoOfIso (asIso (prodComparison SSet.toTop X Y))

@[simp] theorem finiteRightHomeomorph_toContinuousMap (X Y : SSet.{u}) [Y.Finite] :
    ((finiteRightHomeomorph X Y) : C(_, _)) = comparison X Y := rfl

/-- Naturality retains the actual inclusion and its two coordinates. -/
theorem comparison_inclusion (X Y : SSet.{u}) (B : Y.Subcomplex)
    (p : |X ⊗ (B : SSet.{u})|) :
    comparison X Y (SSet.toTop.map (X ◁ B.ι) p) =
      ((comparison X (B : SSet.{u}) p).1,
        SSet.toTop.map B.ι (comparison X (B : SSet.{u}) p).2) :=
  ConcreteCategory.congr_hom
    (prodComparison_natural_whiskerLeft (A := X) SSet.toTop B.ι) p

/-- The canonical comparison is injective. Both points are first represented
in one common finite right subcomplex, where the comparison is invertible. -/
theorem comparison_injective (X Y : SSet.{u}) : Function.Injective (comparison X Y) := by
  intro p q hpq
  obtain ⟨B, hB, p', q', hp, hq⟩ := pair_right_factors p q
  let : SSet.Finite (B : SSet.{u}) := hB
  rw [← hp, ← hq, comparison_inclusion, comparison_inclusion] at hpq
  have hfst := congrArg _root_.Prod.fst hpq
  have hsnd := (realization_mono_isClosedEmbedding B.ι).injective
    (congrArg _root_.Prod.snd hpq)
  have he : comparison X (B : SSet.{u}) p' = comparison X (B : SSet.{u}) q' :=
    _root_.Prod.ext hfst hsnd
  exact hp.symm.trans ((congrArg (SSet.toTop.map (X ◁ B.ι))
    ((finiteRightHomeomorph X (B : SSet.{u})).injective he)).trans hq)

/-- Every compact-source map into the actual topological product lifts
continuously and exactly through the prescribed comparison. -/
theorem comparison_compact_lifts (X Y : SSet.{u}) : HasCompactSourceLifts (comparison X Y) := by
  intro T _ _ f
  obtain ⟨B, hB, g, hg⟩ :=
    realization_continuousMap_factors_finiteSubcomplex (ContinuousMap.snd.comp f)
  let : SSet.Finite (B : SSet.{u}) := hB
  let k : C(T, |X| × |(B : SSet.{u})|) := (ContinuousMap.fst.comp f).prodMk g
  let l : C(T, |X ⊗ (B : SSet.{u})|) :=
    ((finiteRightHomeomorph X (B : SSet.{u})).symm : C(_, _)).comp k
  refine ⟨(SSet.toTop.map (X ◁ B.ι)).hom.comp l, ?_⟩
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, comparison_inclusion]
  have he : comparison X (B : SSet.{u}) (l t) = k t :=
    (finiteRightHomeomorph X (B : SSet.{u})).apply_symm_apply (k t)
  rw [he]
  exact _root_.Prod.ext rfl (DFunLike.congr_fun hg t)

/-- The original comparison induces the genuine based homotopy-group equivalence. -/
def comparisonPiEquiv (X Y : SSet.{u}) (p : |X ⊗ Y|) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) |X ⊗ Y| p ≃*
      HomotopyGroup.Pi (n + 1) (|X| × |Y|) (comparison X Y p) :=
  piEquivOfCompactLifts (comparison X Y) (comparison_injective X Y)
    (comparison_compact_lifts X Y) rfl n

/-- The forward homomorphism is induced by the original product comparison. -/
@[simp] theorem comparisonPiEquiv_coe (X Y : SSet.{u}) (p : |X ⊗ Y|) (n : ℕ) :
    (comparisonPiEquiv X Y p n : HomotopyGroup.Pi (n + 1) |X ⊗ Y| p →*
      HomotopyGroup.Pi (n + 1) (|X| × |Y|) (comparison X Y p)) =
        HomotopyGroup.piMap n (comparison X Y) rfl := rfl

/-- Product of actual realization homotopy groups, with original comparison
followed by the two original topological projections. -/
def piEquiv (X Y : SSet.{u}) (p : |X ⊗ Y|) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) |X ⊗ Y| p ≃*
      HomotopyGroup.Pi (n + 1) |X| (comparison X Y p).1 ×
        HomotopyGroup.Pi (n + 1) |Y| (comparison X Y p).2 :=
  (comparisonPiEquiv X Y p n).trans (piProdEquiv n _ _)

end SSet.ProductRealization

attribute [colib_tag "COL-0220",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(6), page 24"
    "background"
    "Compactly generated nerve products; precise ordinary-topology comparison proved here"]
  SSet.ProductRealization.comparison_injective
  SSet.ProductRealization.comparison_compact_lifts
  SSet.ProductRealization.comparisonPiEquiv
  SSet.ProductRealization.comparisonPiEquiv_coe
  SSet.ProductRealization.finiteRightHomeomorph
