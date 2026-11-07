/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.SkeletalCartesianInduction
public import Colib.CategoryTheory.TheoremB.VertexWeakAssembly

/-!
# Quillen's Theorem B on all based homotopy sets

The actual transition homotopy-equivalence hypothesis now implies the
canonical comma-to-homotopy-fiber comparison is bijective in every finite
homotopy degree, including degree zero. The finite cartesian stage input
is proved by simultaneous skeletal induction, rather than assumed.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/WeakComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; actual comparisons and basepoints are retained. -/
@[expose] public section

open CategoryTheory.TheoremA


noncomputable section
universe u
open CategoryTheory Limits Topology
open scoped Simplicial Topology
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.TheoremB
open TheoremA CategoryTheory.TheoremB.Skeletal
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- At every existing source basepoint, the canonical vertex comparison
induces bijections on all homotopy sets, including degree zero, under the
actual transition homotopy-equivalence hypothesis alone. -/
theorem vertexFiberComparison_bijective_of_transitions
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (d : D) (x : |H.obj d|) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (vertexFiberComparison H d) (x := x) rfl) :=
  vertexFiberComparison_bijective H
    (fun m hm ↦ stageComparisonHomotopyEquiv H htrans 1 m hm)
    (fun m hm ↦ stageComparisonHomotopyEquiv_toFun H htrans 1 m hm) d x n

variable {C : Type u} [SmallCategory C] (F : C ⥤ D)

/-- Quillen's Theorem B at the canonical identity-arrow basepoint, in
every homotopy degree including π₀. All realization, skeletal, colimit,
and basepoint transports are derived from the transition hypothesis. -/
theorem fiberComparison_bijective (h : TransitionHomotopyEquivalences F)
    (c : C) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (fiberComparison F (F.obj c)) (fiberComparison_identity F c)) := by
  have htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |(commaNerveDiagram F).obj d|
          |(commaNerveDiagram F).obj e|,
        E.toFun = (SSet.toTop.map ((commaNerveDiagram F).map f)).hom := by
    intro d e f
    exact ⟨transitionHomotopyEquiv F h f, rfl⟩
  exact fiberComparison_bijective_of_finiteSkeleta F
    (fun m hm ↦ stageComparisonHomotopyEquiv (commaNerveDiagram F) htrans 1 m hm)
    (fun m hm ↦ stageComparisonHomotopyEquiv_toFun (commaNerveDiagram F) htrans 1 m hm) c n

/-- The positive-degree group isomorphism of Theorem B has precisely the
canonical comma-to-fiber map as its forward group homomorphism. -/
def fiberComparisonPiEquiv (h : TransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (ClassifyingSpace (CostructuredArrow F (F.obj c)))
      (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) ≃*
    HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c)))
      (HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c)) :=
  MulEquiv.ofBijective
    (HomotopyGroup.piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c))
    (fiberComparison_bijective F h c (n + 1))

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem fiberComparisonPiEquiv_coe
    (h : TransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    ↑(fiberComparisonPiEquiv F h c n) =
      HomotopyGroup.piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c) := rfl

end CategoryTheory.TheoremB

attribute [colib_tag "COL-0248",
  colib_ref "WeibelKBook" "IV, 3.8, page 31" "adaptation"
    "The original transition homotopy-equivalence theorem, retaining actual comma-to-fiber maps"]
  CategoryTheory.TheoremB.fiberComparison_bijective
  CategoryTheory.TheoremB.fiberComparisonPiEquiv
  CategoryTheory.TheoremB.fiberComparisonPiEquiv_coe

attribute [colib_ref "Quillen1973"
    "Section 1, Theorem B and its dual formulation, p. 97" "adaptation"
    "The canonical costructured comma-to-fiber map under the transition homotopy-equivalence \
      hypothesis"]
  CategoryTheory.TheoremB.fiberComparison_bijective
  CategoryTheory.TheoremB.fiberComparisonPiEquiv
