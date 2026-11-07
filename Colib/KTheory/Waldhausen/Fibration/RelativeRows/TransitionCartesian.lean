/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.LocalFiber
public import Colib.Topology.Realization.SplitFiberCartesian

/-! # The original relative-row ordinal transitions are weakly cartesian

Actual relative additivity and the strictly natural split fiber prove the
complete weak property of each original transition comparison. The supplied
point is the genuine chosen Waldhausen zero. All finite degrees, including
zero, and actual component surjectivity are retained. The global diagonal
fiber theorem still requires a separate gluing argument.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/TransitionCartesian.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{u} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)

/-- The exact commuting square of the original realized tail and restriction maps. -/
theorem rowTransitionSquare :
    (SSet.toTop.map ((tailSRows N).app n)).hom.comp
      (SSet.toTop.map ((relativeSRows N).map α)).hom =
    (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom.comp
      (SSet.toTop.map ((tailSRows N).app m)).hom := by
  simpa only [Functor.map_comp, TopCat.hom_comp] using
    congrArg (fun f ↦ (SSet.toTop.map f).hom) ((tailSRows N).naturality α)

/-- The prescribed original constant-path comparison for an ordinal transition. -/
def rowTransitionComparison : C(|(relativeSRows N).obj m|,
    HomotopyPullback (SSet.toTop.map ((tailSRows N).app n)).hom
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom) :=
  HomotopyPullback.comparison (SSet.toTop.map ((tailSRows N).app n)).hom
    (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
    (SSet.toTop.map ((tailSRows N).app m)).hom
    (SSet.toTop.map ((relativeSRows N).map α)).hom (rowTransitionSquare N α)

@[simp] theorem rowTransitionComparison_apply (x : |(relativeSRows N).obj m|) :
    (rowTransitionComparison N α x).1 =
      (SSet.toTop.map ((tailSRows N).app m) x,
       SSet.toTop.map ((relativeSRows N).map α) x,
       ContinuousMap.const _
         (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)
           (SSet.toTop.map ((tailSRows N).app m) x))) := rfl

/-- Every original relative-row transition is weakly homotopy cartesian,
from the actual degreewise additivity theorem and literal split naturality. -/
theorem rowTransitionComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (rowTransitionComparison N α) := by
  let : PathConnectedSpace |sSet V.cof V.weq| := inferInstanceAs (PathConnectedSpace V.Delooping)
  have hsquare : (relativeSRows N).map α ≫ firstTailSSet N n.unop ≫ snd _ _ =
      firstTailSSet N m.unop ≫ snd _ _ ≫ (ordinarySRows (acyclicStructure N)).map α := by
    rw [firstTailSSet_snd, ← Category.assoc, firstTailSSet_snd]
    exact (tailSRows N).naturality α
  have hsection : (fiberSRows N).app m ≫ (relativeSRows N).map α = (fiberSRows N).app n := by
    simpa using ((fiberSRows N).naturality α).symm
  have h := SSet.SplitRealizationFiber.comparison_isWeakHomotopyEquivalence
    (firstTailSSet N m.unop) (firstTailSSet N n.unop)
    ((fiberSRows N).app m) ((fiberSRows N).app n)
    (tailZeroVertex N m.unop) (tailZeroVertex N n.unop)
    (fiber_firstTailSSet N m.unop) (fiber_firstTailSSet N n.unop)
    ((relativeSRows N).map α) ((ordinarySRows (acyclicStructure N)).map α)
    hsquare hsection
    (firstTailSSetRealizationHomotopyEquiv N m.unop)
    (firstTailSSetRealizationHomotopyEquiv_toFun N m.unop)
    (firstTailSSetRealizationHomotopyEquiv N n.unop)
    (firstTailSSetRealizationHomotopyEquiv_toFun N n.unop) V.kBasepoint
  change IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison (rowFiberProjection N n.unop)
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
      (rowFiberProjection N m.unop) (SSet.toTop.map ((relativeSRows N).map α)).hom _) at h
  have transport
      (p : C(|(relativeSRows N).obj m|, |(ordinarySRows (acyclicStructure N)).obj m|))
      (q : C(|(relativeSRows N).obj n|, |(ordinarySRows (acyclicStructure N)).obj n|))
      (hp : p = (SSet.toTop.map ((tailSRows N).app m)).hom)
      (hq : q = (SSet.toTop.map ((tailSRows N).app n)).hom)
      (w : q.comp (SSet.toTop.map ((relativeSRows N).map α)).hom =
        (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom.comp p)
      (hw : IsWeakHomotopyEquivalence
        (HomotopyPullback.comparison q
          (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
          p (SSet.toTop.map ((relativeSRows N).map α)).hom w)) :
      IsWeakHomotopyEquivalence (rowTransitionComparison N α) := by
    subst p
    subst q
    exact hw
  exact transport _ _ (rowFiberProjection_eq N m.unop)
    (rowFiberProjection_eq N n.unop) _ h

/-- Every original finite based homotopy map is bijective, including dimension zero. -/
theorem rowTransitionComparison_bijective (x : |(relativeSRows N).obj m|) (k : ℕ) :
    Function.Bijective
      (HomotopyGroup.map (N := Fin k) (rowTransitionComparison N α) (x := x) rfl) :=
  (rowTransitionComparison_isWeakHomotopyEquivalence N α).homotopy_bijective x k

end CategoryTheory.Waldhausen.Fibration.RelativeRows
