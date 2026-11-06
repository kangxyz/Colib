/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.PathSubdivision.PoolComparison
public import Colib.Topology.HomotopyPullback.WeakSource
public import Colib.Topology.FiberwiseMappingPath.BaseChangeLifting

/-!
# Exact transport of universal strict-pullback comparison weakness

A map weak after every actual base change transfers the comparison property
from its original source projection to its target projection. The proof uses
the genuine source/path-retaining homotopy-pullback map and its exact square.
It never promotes an ordinary weak equivalence to arbitrary base-change
weakness, nor infers lifting for the target projection.


Implementation provenance:
`Quillen/Topology/HomotopyPullback/UniversalComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology
namespace FiberwiseMappingPath
variable {E F B C D : Type u}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  [TopologicalSpace C] [TopologicalSpace D]

/-- Identity base change recovers the actual original map by its source
and target graph homeomorphisms. -/
theorem isWeakHomotopyEquivalence_of_baseChangedMap_id (q : C(F, B)) (f : C(E, F))
    (h : IsWeakHomotopyEquivalence (baseChangedMap q f (ContinuousMap.id B))) :
    IsWeakHomotopyEquivalence f := by
  have hs := h.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    (HomotopyPullback.graphHomeomorph (q.comp f)).toHomotopyEquiv)
  change IsWeakHomotopyEquivalence
    ((HomotopyPullback.graphHomeomorph q).toHomotopyEquiv.toFun.comp f) at hs
  exact IsWeakHomotopyEquivalence.of_comp_right hs
    (isWeakHomotopyEquivalence_of_homotopyEquiv (HomotopyPullback.graphHomeomorph
      q).toHomotopyEquiv)

/-- An injective change of base changes only the matching proof of an
actual strict pullback. Both original point coordinates remain fixed. -/
def baseChangeEmbeddingHomeomorph (q : C(F, B)) (g : C(D, B))
    (i : C(B, C)) (hi : Function.Injective i) :
    BaseChangedTarget q g ≃ₜ BaseChangedTarget (i.comp q) (i.comp g) where
  toFun z := ⟨z.1,congrArg i z.2⟩
  invFun z := ⟨z.1,hi z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual base-changed original map commutes exactly with the matching
homeomorphisms for an injective base inclusion. -/
theorem baseChangeEmbeddingHomeomorph_naturality (q : C(F, B)) (f : C(E, F))
    (g : C(D, B)) (i : C(B, C)) (hi : Function.Injective i) :
    (baseChangeEmbeddingHomeomorph q g i hi).toHomotopyEquiv.toFun.comp
      (baseChangedMap q f g) =
    (baseChangedMap (i.comp q) f (i.comp g)).comp
      (baseChangeEmbeddingHomeomorph (q.comp f) g i hi).toHomotopyEquiv.toFun := rfl

/-- Weakness proved in the ambient base transfers to the exact original
chart base. No openness or lifting premise is needed for this identification. -/
theorem baseChangedMap_isWeak_of_injective_base (q : C(F, B)) (f : C(E, F))
    (g : C(D, B)) (i : C(B, C)) (hi : Function.Injective i)
    (h : IsWeakHomotopyEquivalence (baseChangedMap (i.comp q) f (i.comp g))) :
    IsWeakHomotopyEquivalence (baseChangedMap q f g) := by
  have hs := h.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    (baseChangeEmbeddingHomeomorph (q.comp f) g i hi).toHomotopyEquiv)
  rw [← baseChangeEmbeddingHomeomorph_naturality q f g i hi] at hs
  exact IsWeakHomotopyEquivalence.of_comp_right hs
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (baseChangeEmbeddingHomeomorph q g i hi).toHomotopyEquiv)

/-- Base change of an actual source homeomorphism is again an actual
homeomorphism, retaining the new parameter exactly. -/
def baseChangedMapHomeomorph (q : C(F, B)) (e : E ≃ₜ F) (g : C(D, B)) :
    BaseChangedSource q (e : C(E,F)) g ≃ₜ BaseChangedTarget q g where
  toFun := baseChangedMap q (e : C(E,F)) g
  invFun z := ⟨(z.1.1,e.symm z.1.2),by simpa using z.2⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl (e.symm_apply_apply z.1.2)
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl (e.apply_symm_apply z.1.2)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem baseChangedMapHomeomorph_toFun (q : C(F, B))
    (e : E ≃ₜ F) (g : C(D, B)) :
    (baseChangedMapHomeomorph q e g).toHomotopyEquiv.toFun =
      baseChangedMap q (e : C(E,F)) g := rfl

end FiberwiseMappingPath
namespace HomotopyPullback
open FiberwiseMappingPath
variable {E F B D : Type u}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace D]

/-- The comparison square retains its parameter, original source image and
full constant path on both sides. -/
theorem strictPullbackInclusion_source_naturality
    (q : C(F, B)) (f : C(E, F)) (g : C(D, B)) :
    (sourceMap g q f).comp (strictPullbackInclusion (q.comp f) g) =
      (strictPullbackInclusion q g).comp (baseChangedMap q f g) := rfl

/-- Sharp transport for one actual base change: original source weakness,
the displayed source comparison and literal base-change weakness suffice. -/
theorem strictPullbackInclusion_isWeak_of_source
    (q : C(F, B)) (f : C(E, F)) (g : C(D, B))
    (hf : IsWeakHomotopyEquivalence f)
    (hs : IsWeakHomotopyEquivalence (strictPullbackInclusion (q.comp f) g))
    (hb : IsWeakHomotopyEquivalence (baseChangedMap q f g)) :
    IsWeakHomotopyEquivalence (strictPullbackInclusion q g) := by
  have h := (sourceMap_isWeakHomotopyEquivalence g q f hf).comp hs
  rw [strictPullbackInclusion_source_naturality] at h
  exact IsWeakHomotopyEquivalence.of_comp_left h hb

end HomotopyPullback
namespace UniversalStrictPullbackComparison
open HomotopyPullback FiberwiseMappingPath
variable {E F B : Type u}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- A sharp universal comparison transfer with its ordinary and actual
base-change weak inputs stated separately. -/
theorem of_source (q : C(F, B)) (f : C(E, F))
    (hf : IsWeakHomotopyEquivalence f)
    (hs : UniversalStrictPullbackComparison (q.comp f))
    (hb : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, B)),
      IsWeakHomotopyEquivalence (baseChangedMap q f g)) :
    UniversalStrictPullbackComparison q :=
  fun D _ g ↦ strictPullbackInclusion_isWeak_of_source q f g hf (hs D g) (hb D g)

/-- Universal actual base-change weakness already includes the ordinary
weakness needed for source transport, by the identity-base graph models. -/
theorem of_baseChanges (q : C(F, B)) (f : C(E, F))
    (hs : UniversalStrictPullbackComparison (q.comp f))
    (hb : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, B)),
      IsWeakHomotopyEquivalence (baseChangedMap q f g)) :
    UniversalStrictPullbackComparison q :=
  of_source q f (isWeakHomotopyEquivalence_of_baseChangedMap_id q f
    (hb B (ContinuousMap.id B))) hs hb

/-- An actual chart homeomorphism transfers universal comparison weakness
without changing the base or assuming a fibration on the chart. -/
theorem of_homeomorph (q : C(F, B)) (e : E ≃ₜ F)
    (hs : UniversalStrictPullbackComparison (q.comp (e : C(E, F)))) :
    UniversalStrictPullbackComparison q :=
  of_baseChanges q (e : C(E,F)) hs (fun _ _ g ↦
    isWeakHomotopyEquivalence_of_homotopyEquiv (baseChangedMapHomeomorph q e g).toHomotopyEquiv)

end UniversalStrictPullbackComparison
end Topology
