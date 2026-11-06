/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseMappingPath.BaseChange
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceCancellation

/-! # Composition and square cancellation for literal base-changed maps

Every construction keeps the new parameter and the original source point.
The square theorem transports only an equality of defining predicates.


Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/BaseChangeComposition.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology
universe u
namespace Topology.FiberwiseMappingPath
variable {A B C E T D : Type u} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace C] [TopologicalSpace E] [TopologicalSpace T] [TopologicalSpace D]

@[simp] theorem baseChangedMap_comp (p : C(E, T)) (g : C(B, E)) (i : C(A, B)) (a : C(D, T)) :
    (baseChangedMap p g a).comp (baseChangedMap (p.comp g) i a) =
      baseChangedMap p (g.comp i) a := rfl

/-- Literal base changes compose, without a preservation theorem for weak maps. -/
theorem baseChangedMap_comp_isWeak (p : C(E, T)) (g : C(B, E)) (i : C(A, B)) (a : C(D, T))
    (hg : IsWeakHomotopyEquivalence (baseChangedMap p g a))
    (hi : IsWeakHomotopyEquivalence (baseChangedMap (p.comp g) i a)) :
    IsWeakHomotopyEquivalence (baseChangedMap p (g.comp i) a) := hg.comp hi

/-- Cancel a genuinely weak left source leg in the original commutative square
following the same displayed base change on all four corners. -/
theorem baseChangedMap_isWeak_of_square (p : C(E, T))
    (i : C(A, B)) (f : C(A, C)) (g : C(B, E)) (j : C(C, E))
    (hsq : g.comp i = j.comp f) (a : C(D, T))
    (hi : IsWeakHomotopyEquivalence (baseChangedMap (p.comp g) i a))
    (hf : IsWeakHomotopyEquivalence (baseChangedMap (p.comp j) f a))
    (hj : IsWeakHomotopyEquivalence (baseChangedMap p j a)) :
    IsWeakHomotopyEquivalence (baseChangedMap p g a) := by
  let es : BaseChangedSource (p.comp g) i a ≃ₜ BaseChangedSource (p.comp j) f a :=
    Homeomorph.setCongr (by
      ext x
      change p (g (i x.2)) = a x.1 ↔ p (j (f x.2)) = a x.1
      have he : g (i x.2) = j (f x.2) := ContinuousMap.congr_fun hsq x.2
      rw [he])
  have he : (baseChangedMap p g a).comp (baseChangedMap (p.comp g) i a) =
      ((baseChangedMap p j a).comp (baseChangedMap (p.comp j) f a)).comp
        es.toHomotopyEquiv.toFun := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (Prod.ext rfl (ContinuousMap.congr_fun hsq x.val.2))
  apply IsWeakHomotopyEquivalence.of_comp_left (f := baseChangedMap (p.comp g) i a) _ hi
  rw [he]
  exact (hj.comp hf).comp (isWeakHomotopyEquivalence_of_homotopyEquiv es.toHomotopyEquiv)

end Topology.FiberwiseMappingPath
