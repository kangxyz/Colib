/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.ContractibleBaseWeak
public import Colib.Topology.HELP.WeakFinite
public import Colib.Topology.HomotopyLifting.OverBaseCorrection
public import Colib.Topology.HomotopyLifting.FiberwiseExtension
public import Colib.Topology.HomotopyLifting.FiberwiseBoundaryCorrection

/-! # Finite vertical cube HELP from weak original strict fibers

Only the actual finite cube-boundary tests are used. Pullback to the supplied
cube and genuine contraction equivalences give an ordinary weak map;
WeakFinite supplies its full finite lift. Stationary correction and genuine
boundary unpadding retain the original base and entire prescribed track.


Implementation provenance:
`Quillen/Topology/HELP/WeakFiberCube.lean`
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
open CubicalTests HomotopyPullback
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
include hp hq

/-- Ordinary strict cube HELP follows from the original fiber weak property
at just the supplied target cube's distinguished base point. -/
theorem weak_strictHELP_on_cube (n : ℕ)
    (a : C(boundary.{u} n, E)) (b : C(cube.{u} n, F))
    (w : f.comp a = b.comp (boundaryInclusion n).hom)
    (hf : IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver p q f sq (q (b (zero n))))) :
    ∃ c : C(cube.{u} n,E),c.comp (boundaryInclusion n).hom = a ∧
      Nonempty ((f.comp c).HomotopyRel b (Set.range (boundaryInclusion n))) := by
  let r := q.comp b
  let P := {z : cube.{u} n × E // p z.2 = r z.1}
  let Q := {z : cube.{u} n × F // q z.2 = r z.1}
  let u : C(P,Q) := strictPullbackMapOver p q f sq r
  have hu : IsWeakHomotopyEquivalence u :=
    HomotopyFiber.weak_of_strictFiber_contraction
      (strictBaseProjection p r) (strictBaseProjection q r) u rfl
      (HomotopyLiftingProperty.baseChange p r hp)
      (HomotopyLiftingProperty.baseChange q r hq) (zero n) (contraction n)
      (strictPullbackMapOver_fiber_weak p q f sq r (zero n) hf)
  let α : C(boundary.{u} n,P) := {
    toFun x := ⟨(x.val,a x),(ContinuousMap.congr_fun sq (a x)).symm.trans
      (congrArg q (ContinuousMap.congr_fun w x))⟩
    continuous_toFun := by fun_prop }
  let β : C(cube.{u} n,Q) := ⟨fun x ↦ ⟨(x,b x),rfl⟩,by fun_prop⟩
  have hαβ : u.comp α = β.comp (boundaryInclusion n).hom := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact Prod.ext rfl (ContinuousMap.congr_fun w x)
  obtain ⟨c,hc,⟨K⟩⟩ := hu.cube_strictHELP n α β hαβ
  let c' : C(cube.{u} n,E) := (strictSourceProjection p r).comp c
  have hc' : c'.comp (boundaryInclusion n).hom = a := by
    ext x
    exact congrArg (fun z : P ↦ z.1.2) (ContinuousMap.congr_fun hc x)
  let J : (f.comp c').Homotopy b := {
    toContinuousMap := (strictSourceProjection q r).comp K.toHomotopy.toContinuousMap
    map_zero_left x := congrArg (fun z : Q ↦ z.1.2) (K.map_zero_left x)
    map_one_left x := congrArg (fun z : Q ↦ z.1.2) (K.map_one_left x) }
  refine ⟨c',hc',⟨{ J with prop' := ?_ }⟩⟩
  intro t x hx
  exact congrArg (fun z : Q ↦ z.1.2) (K.prop t x hx)

/-- The original strict cube comparison can be made exactly vertical while
its whole boundary remains fixed. -/
theorem weak_strictHELP_on_cube_over_base
    (hf : ∀ b : B,IsWeakHomotopyEquivalence (HomotopyFiber.strictMapOver p q f sq b))
    (n : ℕ) (a : C(boundary.{u} n,E)) (b : C(cube.{u} n,F))
    (w : f.comp a = b.comp (boundaryInclusion n).hom) :
    ∃ c : C(cube.{u} n,E),c.comp (boundaryInclusion n).hom = a ∧ p.comp c = q.comp b ∧
      ∃ V : (f.comp c).Homotopy b,HomotopyOver (q.comp b) q V ∧
        ∀ (t : unitInterval) (x : boundary.{u} n),V (t,x.val) = f (a x) := by
  obtain ⟨c,hc,⟨H⟩⟩ := weak_strictHELP_on_cube p q f sq hp hq n a b w (hf _)
  have hfixed : ∀ x,boundaryDuration n x = 0 → ∀ t,H (t,x) = f (c x) := by
    intro x hx t
    exact H.prop t x ⟨⟨x,(boundaryDuration_eq_zero_iff n x).mp hx⟩,rfl⟩
  obtain ⟨c',hbase,hfix,V,hV,hVA⟩ := correct_comparison_over_fixed_zero p q f sq hp hq
    c b H.toHomotopy (boundaryDuration n) hfixed
  refine ⟨c',?_,hbase,V,hV,?_⟩
  · ext x
    exact (hfix x.val (boundaryDuration_boundary n x)).trans (ContinuousMap.congr_fun hc x)
  · intro t x
    exact (hVA x.val (boundaryDuration_boundary n x) t).trans
      (congrArg f (ContinuousMap.congr_fun hc x))

/-- Full prescribed vertical cube HELP from actual weak strict-fiber maps.
The conclusion is limited to these finite tests, including the zero-cube. -/
theorem weak_fullHELP_on_cube_over_base
    (hf : ∀ b : B,IsWeakHomotopyEquivalence (HomotopyFiber.strictMapOver p q f sq b))
    (n : ℕ) (a : C(boundary.{u} n,E)) (b : C(cube.{u} n,F))
    (H : (f.comp a).Homotopy (b.comp (boundaryInclusion n).hom))
    (hH : ∀ t x,q (H (t,x)) = q (b x.val)) :
    ∃ c : C(cube.{u} n,E),c.comp (boundaryInclusion n).hom = a ∧ p.comp c = q.comp b ∧
      ∃ V : (f.comp c).Homotopy b,HomotopyOver (q.comp b) q V ∧
        ∀ (t : unitInterval) (x : boundary.{u} n),V (t,x.val) = H (t,x) := by
  let i := boundaryInclusion.{u} n
  have hi := boundaryInclusion_hep.{u} n
  have hzero : ∀ x,boundaryDuration n x = 0 ↔ x ∈ Set.range i := by
    intro x
    rw [boundaryDuration_eq_zero_iff]
    exact ⟨fun hx ↦ ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ ↦ hy ▸ y.property⟩
  obtain ⟨Q,hQ₀,hQA,hQB⟩ := hq.extend_over_fixed_base _ _ i hi (boundaryDuration n) hzero b
    H.symm.toContinuousMap (fun x ↦ H.symm.map_zero_left x) (fun t x ↦ hH (unitInterval.symm t) x)
  let b' : C(cube.{u} n,F) := ⟨fun x ↦ Q (1,x),by fun_prop⟩
  let T : b.Homotopy b' := {
    toContinuousMap := Q
    map_zero_left := hQ₀
    map_one_left := fun _ ↦ rfl }
  have hT : HomotopyOver (q.comp b) q T := hQB
  have hw : f.comp a = b'.comp i.hom := by
    ext x
    exact ((hQA 1 x).trans (H.symm.map_one_left x)).symm
  obtain ⟨c,hc,hbase,K,hK,hKA⟩ := weak_strictHELP_on_cube_over_base p q f sq hp hq hf n a b' hw
  have hbase' : p.comp c = q.comp b := by
    ext x
    exact (ContinuousMap.congr_fun hbase x).trans (hQB 1 x)
  have hK' : HomotopyOver (q.comp b) q K := fun t x ↦ (hK t x).trans (hQB 1 x)
  let J := K.trans T.symm
  have hJ : HomotopyOver (q.comp b) q J := hK'.trans hT.symm
  let H' : ((f.comp c).comp i.hom).Homotopy (b.comp i.hom) :=
    H.cast (by rw [ContinuousMap.comp_assoc,hc]) rfl
  have hH' : ∀ t x,q (H' (t,x)) = (q.comp b) (i x) := hH
  have hpad : ∀ t x,J (t,i x) = Path.delayReflLeft 0 (H'.evalAt x) t := by
    intro t x
    rw [Path.delayReflLeft_zero]
    simp only [J,ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
    split_ifs
    · exact (hKA _ x).trans (congrArg f (ContinuousMap.congr_fun hc x)).symm
    · change Q (unitInterval.symm _,i x) = H (_,x)
      rw [hQA]
      simp
  obtain ⟨V,hV,hVA⟩ := unpad_boundary_over_fixed_base q hq i hi (boundaryDuration n) hzero
    (q.comp b) J hJ H' hH' hpad
  exact ⟨c,hc,hbase',V,hV,hVA⟩

end Topology
