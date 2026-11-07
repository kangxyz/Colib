/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.SourceSquare

public import Colib.CategoryTheory.TheoremA.ReplacementStageOne
public import Colib.CategoryTheory.TheoremB.ResolutionWeakTransport
public import Colib.CategoryTheory.TheoremA.ContractibleComma

/-!
# Vertex inclusions in the actual comma replacement

The diagram value at a vertex includes into the genuine diagonal
replacement by the constant base chain. Its comparison to the categorical
resolution is exact. The diagonal-to-resolution map is a homotopy
equivalence because both of its source projections are proved equivalences.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/ReplacementVertex.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

open CategoryTheory.TheoremA

noncomputable section
open SSet TopCat Topology CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA
variable {D : Type u} [SmallCategory D]

/-- In the comma case, the vertex inclusion followed by the diagonal
resolution map is exactly the nerve of the categorical fiber inclusion. -/
theorem replacementVertexInclusion_resolution {C : Type u} [SmallCategory C]
    (F : C ⥤ D) (d : D) :
    replacementVertexInclusion (commaNerveDiagram F) d ≫ commaDiagonalToResolution F =
      nerveMap (fiberInclusion F d) := by
  ext p x : 4
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · simp [replacementVertexInclusion, commaDiagonalToResolution,
      commaDiagonalChain, fiberInclusion, nerveMap]
  · intro i j f
    apply Comma.hom_ext <;> simp [replacementVertexInclusion, commaDiagonalToResolution,
      commaDiagonalChain, fiberInclusion, nerveMap]

variable {C : Type u} [SmallCategory C] (F : C ⥤ D)

/-- The actual map from the diagonal comma replacement to the categorical
resolution is a homotopy equivalence with precisely its canonical forward map. -/
def commaDiagonalResolutionHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |replacementDiagonal (commaNerveDiagram F)|
      (ClassifyingSpace (Resolution F)) := by
  let s := diagonalSourceHomotopyEquiv F
  let t := sourceClassifyingHomotopyEquiv F
  let f := (SSet.toTop.map (commaDiagonalToResolution F)).hom
  have hs : t.toFun.comp f = s.toFun := by
    rw [diagonalSourceHomotopyEquiv_toFun, diagonalSourceMap_eq, Functor.map_comp]
    rfl
  apply homotopyEquivWithMap (s.trans t.symm) f
  have h := t.left_inv.symm.comp (ContinuousMap.Homotopic.refl f)
  change f.Homotopic (t.invFun.comp s.toFun)
  rw [← hs]
  exact h

@[simp]
theorem commaDiagonalResolutionHomotopyEquiv_toFun :
    (commaDiagonalResolutionHomotopyEquiv F).toFun =
      (SSet.toTop.map (commaDiagonalToResolution F)).hom := rfl

end CategoryTheory.TheoremA

namespace CategoryTheory.TheoremB
open TheoremA
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- Exact realized compatibility of the replacement vertex and resolution
fiber inclusions. -/
theorem replacementVertex_resolution_realization (d : D) :
    SSet.toTop.map (replacementVertexInclusion (commaNerveDiagram F) d) ≫
      SSet.toTop.map (commaDiagonalToResolution F) =
      classifyingSpaceMap (fiberInclusion F d) := by
  rw [← Functor.map_comp, replacementVertexInclusion_resolution]
  rfl

/-- The canonical diagonal-to-resolution map lies exactly over the base. -/
theorem replacementResolution_square :
    (classifyingSpaceMap (targetProjection F)).hom.comp
      (commaDiagonalResolutionHomotopyEquiv F).toFun =
      (SSet.toTop.map (replacementBaseMap (commaNerveDiagram F))).hom := by
  change (SSet.toTop.map (commaDiagonalToResolution F) ≫
    SSet.toTop.map (nerveMap (targetProjection F))).hom = _
  rw [← Functor.map_comp, commaDiagonalToResolution_target]

/-- The included diagram value lies in the genuine strict fiber of the
actual diagonal projection. -/
theorem replacementVertex_target (d : D) (x : ClassifyingSpace (CostructuredArrow F d)) :
    SSet.toTop.map (replacementBaseMap (commaNerveDiagram F))
      (SSet.toTop.map (replacementVertexInclusion (commaNerveDiagram F) d) x) =
        classifyingSpacePoint d := by
  rw [← commaDiagonalToResolution_target, Functor.map_comp]
  change classifyingSpaceMap (targetProjection F)
    ((SSet.toTop.map (replacementVertexInclusion (commaNerveDiagram F) d) ≫
      SSet.toTop.map (commaDiagonalToResolution F)) x) = _
  rw [replacementVertex_resolution_realization]
  exact resolutionInclusion_target F d x

/-- The actual constant-path comparison for the replacement vertex. -/
def replacementStrictFiberComparison (d : D) :
    C(ClassifyingSpace (CostructuredArrow F d),
      HomotopyFiber (SSet.toTop.map (replacementBaseMap (commaNerveDiagram F))).hom
        (classifyingSpacePoint d)) where
  toFun x := HomotopyFiber.basepoint _ _
    (SSet.toTop.map (replacementVertexInclusion (commaNerveDiagram F) d) x)
    (replacementVertex_target F d x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (SSet.toTop.map (replacementVertexInclusion (commaNerveDiagram F)
      d)).hom.continuous.prodMk
      continuous_const

/-- The actual replacement and resolution fibers are homotopy equivalent,
using the canonical source map and retaining the path without reparameterization. -/
def replacementResolutionFiberEquiv (d : D) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (SSet.toTop.map (replacementBaseMap (commaNerveDiagram F))).hom
        (classifyingSpacePoint d))
      (HomotopyFiber (classifyingSpaceMap (targetProjection F)).hom (classifyingSpacePoint d)) :=
  HomotopyFiber.sourceEquivOfSquare _ _ (commaDiagonalResolutionHomotopyEquiv F)
    (replacementResolution_square F) (classifyingSpacePoint d)

/-- The transfer keeps precisely the strict fiber comparison. -/
theorem replacementResolutionFiberEquiv_comparison (d : D) :
    (replacementResolutionFiberEquiv F d).toFun.comp (replacementStrictFiberComparison F d) =
      resolutionStrictFiberComparison F d := by
  rw [replacementResolutionFiberEquiv, HomotopyFiber.sourceEquivOfSquare_toFun]
  ext x
  apply Subtype.ext
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (replacementVertex_resolution_realization F d) x
  · rfl

/-- All-degree weak comparison at the diagonal replacement vertex transfers
to the actual resolution strict fiber, preserving the exact forward map. -/
theorem resolutionStrictFiber_bijective_of_replacement (d : D)
    (x : ClassifyingSpace (CostructuredArrow F d)) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.map (N := Fin n)
      (replacementStrictFiberComparison F d) (x := x) rfl)) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (resolutionStrictFiberComparison F d) (x := x) rfl) := by
  have he := ContinuousMap.congr_fun (replacementResolutionFiberEquiv_comparison F d) x
  have hb := homotopyGroupMap_bijective_comp
    (replacementStrictFiberComparison F d) (replacementResolutionFiberEquiv F d).toFun
    rfl he n h
    (homotopyGroupMap_bijective_of_homotopyEquiv (replacementResolutionFiberEquiv F d) he n)
  have hm : HomotopyGroup.map (N := Fin n)
      ((replacementResolutionFiberEquiv F d).toFun.comp (replacementStrictFiberComparison F d))
      (x := x) he =
      HomotopyGroup.map (resolutionStrictFiberComparison F d) (x := x) rfl := by
    funext a
    refine Quotient.inductionOn a (fun p ↦ ?_)
    apply congrArg Quotient.mk'
    apply GenLoop.ext
    intro t
    exact ContinuousMap.congr_fun (replacementResolutionFiberEquiv_comparison F d) (p t)
  rw [hm] at hb
  exact hb

/-- At the identity comma object, weak replacement-vertex comparison gives
the exact canonical original homotopy-fiber comparison in every degree. -/
theorem fiberComparison_bijective_of_replacement (c : C) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.map (N := Fin n)
      (replacementStrictFiberComparison F (F.obj c))
      (x := classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) rfl)) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (fiberComparison F (F.obj c)) (fiberComparison_identity F c)) :=
  fiberComparison_bijective_of_resolutionStrict F c n
    (resolutionStrictFiber_bijective_of_replacement F (F.obj c) _ n h)

end CategoryTheory.TheoremB
