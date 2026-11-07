/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.StrictComparison
public import Colib.Topology.HomotopyLifting.Compact.Stationary
public import Colib.Topology.HELP.StrictFiniteCriterion

/-!
# Strict pullback comparison from compact homotopy lifting

Compact homotopy lifting for the original map suffices for its canonical
strict-to-homotopy-pullback comparison to be a complete weak equivalence
after arbitrary base change. Only compact locally compact test families
are lifted. In particular, the entire homotopy pullback is never used as
a lifting parameter, and no continuous global homotopy inverse is asserted.

The relative construction keeps the parameter, lifts the original stored
path, and uses its literal remaining tail. Stationary correction fixes the
whole cube boundary. Strict finite HELP then supplies full finite HELP and
the empty-aware weak property, including the genuine zero-dimensional test.


Implementation provenance:
`Quillen/Topology/HomotopyPullback/CompactComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
open unitInterval
universe u

namespace Topology
variable {E B X : Type u}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]

/-- Compact covering-homotopy lifting is preserved by arbitrary base change.
The base-change space itself needs no compactness hypothesis. -/
theorem CompactHomotopyLiftingProperty.baseChange
    (p : C(E, B)) (f : C(X, B)) (hp : CompactHomotopyLiftingProperty p) :
    CompactHomotopyLiftingProperty (HomotopyPullback.strictBaseProjection p f) := by
  intro D _ _ _ a H hzero
  let a' : C(D,E) := ⟨fun x ↦ (a x).1.2,by fun_prop⟩
  obtain ⟨L,hL₀,hL⟩ := hp D a' (f.comp H) (fun x ↦ by
    change f (H (0,x)) = p (a x).1.2
    rw [hzero]
    exact (a x).2.symm)
  let L' : C(I × D,{z : X × E // p z.2 = f z.1}) :=
    ⟨fun z ↦ ⟨(H z,L z),hL z.1 z.2⟩,by fun_prop⟩
  refine ⟨L',?_,fun _ _ ↦ rfl⟩
  intro x
  apply Subtype.ext
  exact Prod.ext (hzero x) (hL₀ x)

namespace HomotopyPullback
variable (p : C(E, B)) (f : C(X, B))

@[simp] theorem strictPullbackInclusion_parameter
    (z : {z : X × E // p z.2 = f z.1}) :
    (strictPullbackInclusion p f z).1.1 = z.1.1 := rfl

@[simp] theorem strictPullbackInclusion_source
    (z : {z : X × E // p z.2 = f z.1}) :
    (strictPullbackInclusion p f z).1.2.1 = z.1.2 := rfl

@[simp] theorem strictPullbackInclusion_path
    (z : {z : X × E // p z.2 = f z.1}) (t : I) :
    (strictPullbackInclusion p f z).1.2.2 t = f z.1.1 := rfl

/-- A compact family of original source/path pairs can be moved into the
strict pullback relative to a specified zero locus of constant paths.
The initial source and entire original path remain the endpoints of the
displayed homotopy; the base-change parameter stays unchanged. -/
theorem strictPullbackInclusion_compact_relative
    (hp : CompactHomotopyLiftingProperty p)
    {D : Type u} [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
    (b : C(D, HomotopyPullback p f)) (duration : C(D, I))
    (hfixed : ∀ x, duration x = 0 → ∀ t, (b x).1.2.2 t = p (b x).1.2.1) :
    ∃ c : C(D,{z : X × E // p z.2 = f z.1}),
      (∀ x,(c x).1.1 = (b x).1.1) ∧
      (∀ x,duration x = 0 → (c x).1.2 = (b x).1.2.1) ∧
      ∃ K : b.HomotopyRel ((strictPullbackInclusion p f).comp c)
        {x | duration x = 0},
          ∀ t x,(K (t,x)).1.1 = (b x).1.1 := by
  let a := (sourceProjection p f).comp b
  let H : C(I × D,B) := ⟨fun z ↦ (b z.2).1.2.2 z.1,by fun_prop⟩
  obtain ⟨L,hL₀,hL,hLfixed⟩ := hp.lift_fixed_zero a H
    (fun x ↦ (b x).2.1) duration hfixed
  let c : C(D,{z : X × E // p z.2 = f z.1}) := {
    toFun x := ⟨((b x).1.1,L (1,x)),(hL 1 x).trans (b x).2.2⟩
    continuous_toFun := by fun_prop }
  let K : b.Homotopy ((strictPullbackInclusion p f).comp c) := {
    toFun z := ⟨((b z.2).1.1,L z,
      ⟨fun s ↦ (b z.2).1.2.2 (σ (σ z.1 * σ s)),by fun_prop⟩),
      by simpa [H] using (hL z.1 z.2).symm,
      by simpa using (b z.2).2.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · fun_prop
      · apply Continuous.prodMk L.continuous
        apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun z : (I × D) × I ↦
          (b z.1.2).1.2.2 (σ (σ z.1.1 * σ z.2)))
        fun_prop
    map_zero_left x := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      refine Prod.ext (hL₀ x) ?_
      ext s
      simp
    map_one_left x := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      refine Prod.ext rfl ?_
      ext s
      change (b x).1.2.2 (σ (σ 1 * σ s)) = f (b x).1.1
      simpa using (b x).2.2 }
  refine ⟨c,fun _ ↦ rfl,fun x hx ↦ hLfixed x hx 1,{ K with prop' := ?_ },
    fun _ _ ↦ rfl⟩
  intro t x hx
  apply Subtype.ext
  refine Prod.ext rfl ?_
  refine Prod.ext (hLfixed x hx t) ?_
  ext s
  exact (hfixed x hx _).trans (hfixed x hx s).symm

/-- Literal strict finite cube HELP for the original constant-path
comparison. There is no compactness assumption on the base-change space. -/
theorem strictPullbackInclusion_finiteCubeStrictHELP
    (hp : CompactHomotopyLiftingProperty p) :
    FiniteCubeStrictHELP (strictPullbackInclusion p f) := by
  intro n a b w
  have hw (x : CubicalTests.boundary.{u} n) :
      strictPullbackInclusion p f (a x) = b x.val := ContinuousMap.congr_fun w x
  have hfixed : ∀ x,CubicalTests.boundaryDuration n x = 0 →
      ∀ t,(b x).1.2.2 t = p (b x).1.2.1 := by
    intro x hx t
    let z : CubicalTests.boundary.{u} n :=
      ⟨x,(CubicalTests.boundaryDuration_eq_zero_iff n x).mp hx⟩
    change (b z.val).1.2.2 t = p (b z.val).1.2.1
    rw [← hw z]
    exact (a z).2.symm
  obtain ⟨c,hparam,hsource,K,_⟩ := strictPullbackInclusion_compact_relative p f hp
    b (CubicalTests.boundaryDuration n) hfixed
  refine ⟨c,?_,⟨{ K.symm.toHomotopy with prop' := ?_ }⟩⟩
  · apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact (hparam x.val).trans (congrArg (fun z : HomotopyPullback p f ↦ z.1.1)
        (hw x)).symm
    · exact (hsource x.val (CubicalTests.boundaryDuration_boundary n x)).trans
        (congrArg (fun z : HomotopyPullback p f ↦ z.1.2.1) (hw x)).symm
  · intro t x hx
    obtain ⟨z,rfl⟩ := hx
    exact K.symm.prop t z.val (CubicalTests.boundaryDuration_boundary n z)

/-- Full prescribed-boundary finite HELP of the same original comparison. -/
theorem strictPullbackInclusion_finiteCubeHELP
    (hp : CompactHomotopyLiftingProperty p) :
    FiniteCubeHELP (strictPullbackInclusion p f) :=
  (strictPullbackInclusion_finiteCubeStrictHELP p f hp).full

/-- Compact HLP of the original map makes its strict pullback comparison
a complete weak homotopy equivalence after every arbitrary base change.
This includes component surjectivity and every finite based homotopy set. -/
theorem strictPullbackInclusion_isWeakHomotopyEquivalence_of_compact
    (hp : CompactHomotopyLiftingProperty p) :
    IsWeakHomotopyEquivalence (strictPullbackInclusion p f) :=
  (strictPullbackInclusion_finiteCubeStrictHELP p f hp).isWeakHomotopyEquivalence

end HomotopyPullback
end Topology
