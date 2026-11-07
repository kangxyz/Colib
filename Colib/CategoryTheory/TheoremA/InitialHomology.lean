/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremA.ReplacementHomology
public import Colib.CategoryTheory.TheoremA.InitialReplacement
public import Colib.CategoryTheory.TheoremA.ConstantNerveReplacement
public import Colib.CategoryTheory.TheoremA.ContractibleComma
public import Colib.Topology.LocalCoefficients.MapQuasiIso

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/InitialHomology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Original twisted comma comparison over a specified initial base object

The canonical initial-object diagram transformation, the genuine constant-entry
homotopy equivalence, and the original source augmentation prove the comparison
for the actual comma projection. Only homology comparison of the original
initial-object transitions is required; no homology-fibration criterion is an input.
-/

@[expose] public section
noncomputable section
open SSet TopCat Convexity.StdSimplex
open CategoryTheory Limits FundamentalGroupoid.LocalCoefficients
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- The original initial comma entry preserves every abelian target local system. -/
theorem commaInitialReplacementEntry_abelian_quasiIso (F : C ⥤ D) (i : D)
    (hi : IsInitial i)
    (htrans : ∀ (d : D) (B : System.{u, u} |(commaNerveDiagram F).obj d|),
      AbelianMonodromy B → QuasiIso (pushforwardChainMap
        (SSet.toTop.map ((commaNerveDiagram F).map (hi.to d))).hom B))
    (A : System.{u, u} |replacementDiagonal (commaNerveDiagram F)|)
    (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (SSet.toTop.map (replacementEntry (commaNerveDiagram F) i)).hom A) := by
  let H := commaNerveDiagram F
  let q := (SSet.toTop.map (diagonalMap
    (simplicialReplacementMap (initialReplacementComparison H i hi)))).hom
  let j := (SSet.toTop.map (replacementEntry ((Functor.const D).obj (H.obj i)) i)).hom
  have hq : QuasiIso (pushforwardChainMap q A) :=
    replacementRealization_abelian_quasiIso (initialReplacementComparison H i hi)
      htrans A hA
  have hj : QuasiIso (pushforwardChainMap j (pullback q A)) := by
    have h := pushforwardChainMap_quasiIso_of_homotopyEquiv
      (constantNerveReplacementEntryHomotopyEquiv (CostructuredArrow F i) i hi) (pullback q A)
    rw [constantNerveReplacementEntryHomotopyEquiv_toFun] at h
    exact h
  have hcomp := pushforwardChainMap_quasiIso_comp j q A hj hq
  have hw : q.comp j = (SSet.toTop.map (replacementEntry H i)).hom := by
    change (SSet.toTop.map (replacementEntry ((Functor.const D).obj (H.obj i)) i) ≫
      SSet.toTop.map (diagonalMap
        (simplicialReplacementMap (initialReplacementComparison H i hi)))).hom = _
    rw [← Functor.map_comp, initialReplacementComparison_entry]
  rw [hw] at hcomp
  exact hcomp

/-- The original comma projection at the initial object is an abelian twisted
homology equivalence when the original initial-object comma transitions are. -/
theorem commaInitialProjection_abelian_quasiIso (F : C ⥤ D) (i : D) (hi : IsInitial i)
    (htrans : ∀ (d : D) (B : System.{u, u} |(commaNerveDiagram F).obj d|),
      AbelianMonodromy B → QuasiIso (pushforwardChainMap
        (SSet.toTop.map ((commaNerveDiagram F).map (hi.to d))).hom B))
    (A : System.{u, u} (ClassifyingSpace C)) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (SSet.toTop.map (nerveMap (CostructuredArrow.proj F i))).hom A) := by
  let q := (SSet.toTop.map (diagonalSourceMap F)).hom
  let j := (SSet.toTop.map (replacementEntry (commaNerveDiagram F) i)).hom
  have hq : QuasiIso (pushforwardChainMap q A) := by
    have h := pushforwardChainMap_quasiIso_of_homotopyEquiv (diagonalSourceHomotopyEquiv F) A
    rw [diagonalSourceHomotopyEquiv_toFun] at h
    exact h
  have hj : QuasiIso (pushforwardChainMap j (pullback q A)) :=
    commaInitialReplacementEntry_abelian_quasiIso F i hi htrans (pullback q A)
      (pullback_abelianMonodromy q hA)
  have hcomp := pushforwardChainMap_quasiIso_comp j q A hj hq
  have hw : q.comp j = (SSet.toTop.map (nerveMap (CostructuredArrow.proj F i))).hom := by
    change (SSet.toTop.map (replacementEntry (commaNerveDiagram F) i) ≫
      SSet.toTop.map (diagonalSourceMap F)).hom = _
    rw [← Functor.map_comp, replacementEntry_diagonalSourceMap]
  rw [hw] at hcomp
  exact hcomp

end CategoryTheory.TheoremA
