/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.ContractibleTestOverBase
public import Colib.Topology.HomotopyLifting.FiberwiseExtension
public import Colib.Topology.HomotopyLifting.FiberwiseBoundaryCorrection

/-! # Full compact contracted HELP over the displayed base

The exact originally prescribed boundary homotopy is retained, including all
its intermediate points. Fiberwise HEP and actual vertical unpadding derive
this from strict over-base HELP, rather than assuming that ordinary HELP was
already fiberwise.


Implementation provenance:
`Quillen/Topology/HELP/ContractibleTestFullOverBase.lean`
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

theorem fullHELP_over_contracted_test
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B,CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b))
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (a : C(A,E)) (b : C(D,F)) (H : (f.comp a).Homotopy (b.comp i.hom))
    (hH : ∀ t x,q (H (t,x)) = q (b (i x))) :
    ∃ c : C(D,E),c.comp i.hom = a ∧ p.comp c = q.comp b ∧
      ∃ V : (f.comp c).Homotopy b,
        HomotopyOver (q.comp b) q V ∧ ∀ t x,V (t,i x) = H (t,x) := by
  obtain ⟨Q,hQ₀,hQA,hQB⟩ := hq.extend_over_fixed_base A D i hi duration hzero b
    H.symm.toContinuousMap (fun x ↦ H.symm.map_zero_left x) (fun t x ↦ hH (unitInterval.symm t) x)
  let b' : C(D,F) := ⟨fun x ↦ Q (1,x),by fun_prop⟩
  let T : b.Homotopy b' := {
    toContinuousMap := Q
    map_zero_left := hQ₀
    map_one_left := fun _ ↦ rfl }
  have hT : HomotopyOver (q.comp b) q T := hQB
  have hw : f.comp a = b'.comp i.hom := by
    ext x
    exact ((hQA 1 x).trans (H.symm.map_one_left x)).symm
  obtain ⟨c,hc,hbase,K,hK,hKA⟩ := strictHELP_over_contracted_test p q f sq hp hq hf
    A D i hi d₀ HD duration hzero a b' hw
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
  obtain ⟨V,hV,hVA⟩ := unpad_boundary_over_fixed_base q hq i hi duration hzero
    (q.comp b) J hJ H' hH' hpad
  exact ⟨c,hc,hbase',V,hV,hVA⟩

end Topology
