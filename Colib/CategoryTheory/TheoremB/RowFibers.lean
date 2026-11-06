/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.Rows
public import Colib.Topology.HomotopyFiber.DiscreteBase
public import Colib.Topology.HomotopyFiber.Map

/-!
# Actual homotopy fibers of the simplicial-replacement rows

Every row projects to a discrete space of base chains. Its actual path-space
homotopy fiber is its chosen comma summand. Under Theorem B's hypothesis,
every simplex operator induces a genuine homotopy equivalence of these
actual row fibers. The forward maps are the canonical maps of fibers.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/RowFibers.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual comma categories, nerves and
path-space maps are retained; no fiber-equivalence conclusion is assumed. -/
@[expose] public section


noncomputable section

open Topology CategoryTheory Opposite
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.TheoremB

section Coproducts

variable {ι κ : Type u} [TopologicalSpace ι] [DiscreteTopology ι]
  [TopologicalSpace κ] [DiscreteTopology κ]
  {X : ι → Type u} {Y : κ → Type u}
  [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]

/-- The canonical map on actual fibers of reindexed coproduct projections. -/
def sigmaFiberMap (a : ι → κ) (f : ∀ i, C(X i, Y (a i))) (i : ι) :
    C(HomotopyFiber (sigmaProjection X) i, HomotopyFiber (sigmaProjection Y) (a i)) :=
  HomotopyFiber.map (f₁ := sigmaProjection X) (f₂ := sigmaProjection Y)
    (sigmaReindexContinuousMap a f) ⟨a, continuous_of_discreteTopology⟩ rfl i

/-- The map of fibers acts as the prescribed component map under the actual
fiber homeomorphisms. -/
theorem sigmaFiberMap_homeomorph (a : ι → κ) (f : ∀ i, C(X i, Y (a i))) (i : ι)
    (z : HomotopyFiber (sigmaProjection X) i) :
    sigmaProjectionFiberHomeomorph Y (a i) (sigmaFiberMap a f i z) =
      f i (sigmaProjectionFiberHomeomorph X i z) := by
  obtain ⟨x, rfl⟩ := (sigmaProjectionFiberHomeomorph X i).symm.surjective z
  rfl

/-- A component homotopy equivalence gives a genuine homotopy equivalence
between the actual fibers of the corresponding coproduct projections. -/
def sigmaFiberHomotopyEquiv (a : ι → κ)
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y (a i))) (i : ι) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (sigmaProjection X) i) (HomotopyFiber (sigmaProjection Y) (a i)) :=
  ((sigmaProjectionFiberHomeomorph X i).toHomotopyEquiv.trans (e i)).trans
    (sigmaProjectionFiberHomeomorph Y (a i)).symm.toHomotopyEquiv

/-- Its forward map is exactly the canonical map on path-space fibers. -/
theorem sigmaFiberHomotopyEquiv_toFun (a : ι → κ)
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y (a i))) (i : ι) :
    (sigmaFiberHomotopyEquiv a e i).toFun = sigmaFiberMap a (fun i ↦ (e i).toFun) i := by
  apply ContinuousMap.ext
  intro z
  apply (sigmaProjectionFiberHomeomorph Y (a i)).injective
  change sigmaProjectionFiberHomeomorph Y (a i)
    ((sigmaProjectionFiberHomeomorph Y (a i)).symm
      (e i (sigmaProjectionFiberHomeomorph X i z))) = _
  rw [Homeomorph.apply_symm_apply, sigmaFiberMap_homeomorph]

end Coproducts

variable (D : Type u) [SmallCategory D]

/-- The discrete topological space of base chains in a given simplicial degree. -/
def ChainSpace (p : SimplexCategoryᵒᵖ) : TopCat.{u} :=
  @TopCat.of ((nerve D).obj p) ⊥

instance chainSpace_discrete (p : SimplexCategoryᵒᵖ) : DiscreteTopology (ChainSpace D p) := ⟨rfl⟩

variable {D} {C : Type u} [SmallCategory C] (F : C ⥤ D)

/-- The actual projection from a topological comma-replacement row to its
(discrete) space of base chains. -/
def commaRowProjection (p : SimplexCategoryᵒᵖ) :
    C((Σ s : ChainSpace D p, ClassifyingSpace (CostructuredArrow F (s.obj 0))), ChainSpace D p) :=
  sigmaProjection fun s : ChainSpace D p ↦ ClassifyingSpace (CostructuredArrow F (s.obj 0))

/-- The canonical fiber map attached to any simplicial operator on the comma replacement. -/
def commaRowFiberMap {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (s : ChainSpace D p) :
    C(HomotopyFiber (commaRowProjection F p) s,
      HomotopyFiber (commaRowProjection F q) ((nerve D).map α s)) :=
  sigmaFiberMap (ι := ChainSpace D p) (κ := ChainSpace D q)
    (X := fun s : ChainSpace D p ↦ ClassifyingSpace (CostructuredArrow F (s.obj 0)))
    (Y := fun s : ChainSpace D q ↦ ClassifyingSpace (CostructuredArrow F (s.obj 0)))
    (fun s ↦ (nerve D).map α s)
    (fun s ↦ transitionMap F (TheoremA.firstVertexEdge α s)) s

/-- The row-fiber map lies over the actual topological replacement map. -/
@[simp]
theorem commaRowFiberMap_projection {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    (s : ChainSpace D p) :
    (HomotopyFiber.projection (commaRowProjection F q) ((nerve D).map α s)).comp
      (commaRowFiberMap F α s) =
      (topologicalRowMap (TheoremA.commaNerveDiagram F) α).comp
        (HomotopyFiber.projection (commaRowProjection F p) s) := rfl

/-- The coproduct projection is the component of the genuine simplicial-space
projection to the discrete nerve. -/
@[simp]
theorem commaRowProjection_eq (p : SimplexCategoryᵒᵖ) :
    (topologicalReplacementProjection (TheoremA.commaNerveDiagram F)).app p =
      TopCat.ofHom (commaRowProjection F p) := rfl

/-- Under precisely Theorem B's transition hypothesis, every actual row-fiber
map induced by a simplex operator is a genuine homotopy equivalence. -/
def commaRowFiberHomotopyEquiv (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (s : ChainSpace D p) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (commaRowProjection F p) s)
      (HomotopyFiber (commaRowProjection F q) ((nerve D).map α s)) :=
  sigmaFiberHomotopyEquiv (ι := ChainSpace D p) (κ := ChainSpace D q)
    (X := fun s : ChainSpace D p ↦ ClassifyingSpace (CostructuredArrow F (s.obj 0)))
    (Y := fun s : ChainSpace D q ↦ ClassifyingSpace (CostructuredArrow F (s.obj 0)))
    (fun s ↦ (nerve D).map α s)
    (fun s ↦ transitionHomotopyEquiv F h (TheoremA.firstVertexEdge α s)) s

/-- The row-fiber equivalence retains the canonical map as its forward map. -/
@[simp]
theorem commaRowFiberHomotopyEquiv_toFun (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (s : ChainSpace D p) :
    (commaRowFiberHomotopyEquiv F h α s).toFun = commaRowFiberMap F α s :=
  sigmaFiberHomotopyEquiv_toFun _ _ _

end CategoryTheory.TheoremB
