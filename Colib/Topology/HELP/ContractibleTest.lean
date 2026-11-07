/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.StrictPullback
public import Colib.Topology.HomotopyFiber.ContractibleBaseHELP

/-! # Strict HELP on actual compact contracted test spaces

Pull both genuine fibrations back along the supplied target map's base
coordinate. Their original strict-fiber transition has compact HELP after
the actual fiber homeomorphisms, so the contracted-base theorem gives HELP
of the literal pullback map. Project its strict lift and relative homotopy
back to the original spaces. No over-base correction or gluing is asserted.


Implementation provenance:
`Quillen/Topology/HELP/ContractibleTest.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology
open HomotopyPullback
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
include hp hq

/-- Strict-square HELP for a compact HEP pair whose target has a displayed
contraction. Only the actual fiber over the contracted test's chosen target
point needs compact HELP. The lift extends the boundary exactly, and the
comparison homotopy is relative to the whole boundary image. -/
theorem strictHELP_on_contracted_test
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (α : C(A, E)) (β : C(D, F)) (w : f.comp α = β.comp i.hom)
    (hf : CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq (q (β d₀)))) :
    ∃ c : C(D, E), c.comp i.hom = α ∧
      Nonempty ((f.comp c).HomotopyRel β (Set.range i)) := by
  let r := q.comp β
  let P := {z : D × E // p z.2 = r z.1}
  let Q := {z : D × F // q z.2 = r z.1}
  let u : C(P, Q) := strictPullbackMapOver p q f sq r
  have hu : CompactHomotopyExtensionLiftingProperty u :=
    HomotopyFiber.compactHELP_of_strictFiber_contraction
      (strictBaseProjection p r) (strictBaseProjection q r) u rfl
      (HomotopyLiftingProperty.baseChange p r hp)
      (HomotopyLiftingProperty.baseChange q r hq) d₀ HD
      (strictPullbackMapOver_fiber_compactHELP p q f sq r d₀ hf)
  let a : C(A, P) := {
    toFun x := ⟨(i x, α x), (ContinuousMap.congr_fun sq (α x)).symm.trans
      (congrArg q (ContinuousMap.congr_fun w x))⟩
    continuous_toFun := by fun_prop }
  let b : C(D, Q) := ⟨fun x ↦ ⟨(x, β x), rfl⟩, by fun_prop⟩
  have hab : u.comp a = b.comp i.hom := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact Prod.ext rfl (ContinuousMap.congr_fun w x)
  obtain ⟨c, hc, ⟨K⟩⟩ := hu.strict A D i hi a b hab
  let c' : C(D, E) := (strictSourceProjection p r).comp c
  have hc' : c'.comp i.hom = α := by
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun z : P ↦ z.1.2) (ContinuousMap.congr_fun hc x)
  let J : (f.comp c').Homotopy β := {
    toContinuousMap := (strictSourceProjection q r).comp K.toHomotopy.toContinuousMap
    map_zero_left x := congrArg (fun z : Q ↦ z.1.2) (K.map_zero_left x)
    map_one_left x := congrArg (fun z : Q ↦ z.1.2) (K.map_one_left x) }
  refine ⟨c', hc', ⟨{ J with prop' := ?_ }⟩⟩
  intro t x hx
  exact congrArg (fun z : Q ↦ z.1.2) (K.prop t x hx)

/-- In the usual pointwise-fiber form, all actual strict-fiber maps have
compact HELP. This gives the original strict lifting problem on every
compact contracted target, without a global gluing premise. -/
theorem strictHELP_on_contracted_test_of_all_fibers
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b))
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (α : C(A, E)) (β : C(D, F)) (w : f.comp α = β.comp i.hom) :
    ∃ c : C(D, E), c.comp i.hom = α ∧
      Nonempty ((f.comp c).HomotopyRel β (Set.range i)) :=
  strictHELP_on_contracted_test p q f sq hp hq A D i hi d₀ HD α β w (hf _)

/-- The same strict lift with the complete constant boundary homotopy
spelled out literally at every time, rather than only at its endpoints. -/
theorem strictHELP_on_contracted_test_boundary
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (α : C(A, E)) (β : C(D, F)) (w : f.comp α = β.comp i.hom)
    (hf : CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq (q (β d₀)))) :
    ∃ c : C(D, E), c.comp i.hom = α ∧ ∃ K : (f.comp c).Homotopy β,
      ∀ t x, K (t, i x) = f (α x) := by
  obtain ⟨c, hc, ⟨K⟩⟩ := strictHELP_on_contracted_test p q f sq hp hq A D i hi d₀ HD α β w hf
  exact ⟨c, hc, K.toHomotopy, fun t x ↦ (K.prop t (i x) ⟨x, rfl⟩).trans
    (congrArg f (ContinuousMap.congr_fun hc x))⟩

end Topology
