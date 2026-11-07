/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.ContractibleTest
public import Colib.Topology.HomotopyLifting.OverBaseCorrection

/-! # Compact contracted strict HELP with a proved vertical comparison

The actual parameter pair has HEP and a continuous duration whose zero locus
is exactly its image. The conclusion retains the original boundary map, the
entire constant boundary comparison, and the displayed base coordinate.


Implementation provenance:
`Quillen/Topology/HELP/ContractibleTestOverBase.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

theorem strictHELP_over_contracted_test
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b))
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (a : C(A,E)) (b : C(D,F)) (w : f.comp a = b.comp i.hom) :
    ∃ c : C(D,E),c.comp i.hom = a ∧ p.comp c = q.comp b ∧
      ∃ V : (f.comp c).Homotopy b,
        HomotopyOver (q.comp b) q V ∧ ∀ t x,V (t,i x) = f (a x) := by
  obtain ⟨c,hc,⟨H⟩⟩ := strictHELP_on_contracted_test_of_all_fibers p q f sq hp hq hf
    A D i hi d₀ HD a b w
  have hfixed : ∀ x,duration x = 0 → ∀ t,H (t,x) = f (c x) :=
    fun x hx t ↦ H.prop t x ((hzero x).mp hx)
  obtain ⟨c',hbase,hfix,V,hV,hVfix⟩ := correct_comparison_over_fixed_zero p q f sq hp hq
    c b H.toHomotopy duration hfixed
  refine ⟨c',?_,hbase,V,hV,?_⟩
  · ext x
    exact (hfix (i x) ((hzero (i x)).mpr ⟨x,rfl⟩)).trans (ContinuousMap.congr_fun hc x)
  · intro t x
    exact (hVfix (i x) ((hzero (i x)).mpr ⟨x,rfl⟩) t).trans
      (congrArg f (ContinuousMap.congr_fun hc x))

end Topology
