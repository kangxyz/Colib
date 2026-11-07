/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CubicalSubdivision.SubspaceNormalization

/-!
# The two-chart face step with every original chart constraint

A face already mapped into the overlap is left pointwise fixed. Otherwise normalization is
performed inside its original chart. The alternative original chart constraint is retained,
not arbitrarily discarded. The entire supplied boundary homotopy and both endpoint support
conditions survive this actual local step.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/TwoChartFaceNormalization.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

open scoped Topology unitInterval

universe u

namespace Topology.CubicalSubdivision

/-- The actual two-chart local normalization, with all original chart constraints and all
boundary times retained. The finite hypotheses concern the literal overlap inclusions. -/
theorem exists_face_two_chart_normalization {n m : ℕ} (F : FaceIndex n m)
    {Y : Type u} [TopologicalSpace Y] (U V : Set Y)
    (a b c e : unitInterval) (hab : a < b) (hce : c < e) (p q : ℕ)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (f : C((Active F → unitInterval), Y))
    (hf : (∀ s, f s ∈ U) ∨ ∀ s, f s ∈ V)
    (H : C(unitInterval ×
      {x : Active F → unitInterval // x ∈ _root_.Cube.boundary (Active F)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val)
    (hHU : (∀ s, f s ∈ U) → ∀ t z, H (t, z) ∈ U)
    (hHV : (∀ s, f s ∈ V) → ∀ t z, H (t, z) ∈ V)
    (hHfix : (∀ s, f s ∈ U ∩ V) → ∀ t z, H (t, z) = f z.val)
    (hSU : (∀ s, f s ∈ U) → ∀ z, H (1, z) ∉ V → z.val ∈ faceThinSupport F a b (p + 1))
    (hSV : (∀ s, f s ∈ V) → ∀ z, H (1, z) ∉ U → z.val ∈ faceThinSupport F c e (q + 1)) :
    ∃ g : C((Active F → unitInterval), Y), ∃ K : f.Homotopy g,
      (∀ t z, K (t, z.val) = H (t, z)) ∧
      ((∀ s, f s ∈ U) → ∀ t s, K (t, s) ∈ U) ∧
      ((∀ s, f s ∈ V) → ∀ t s, K (t, s) ∈ V) ∧
      ((∀ s, f s ∈ U ∩ V) → ∀ t s, K (t, s) = f s) ∧
      ((∀ s, f s ∈ U) → g ⁻¹' Vᶜ ⊆ faceThinSupport F a b (p + 1)) ∧
      ((∀ s, f s ∈ V) → g ⁻¹' Uᶜ ⊆ faceThinSupport F c e (q + 1)) := by
  classical
  by_cases hboth : (∀ s, f s ∈ U) ∧ ∀ s, f s ∈ V
  · refine ⟨f, ContinuousMap.Homotopy.refl f, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t z
      exact (hHfix (fun s ↦ ⟨hboth.1 s, hboth.2 s⟩) t z).symm
    · intro _ _ s
      exact hboth.1 s
    · intro _ _ s
      exact hboth.2 s
    · intros
      rfl
    · intro _ s hs
      exact (hs (hboth.2 s)).elim
    · intro _ s hs
      exact (hs (hboth.1 s)).elim
  · rcases hf with hU | hV
    · obtain ⟨g, K, hK, hKU, hg⟩ := exists_face_subspace_normalization F U V a b hab p hUV
        f hU H (hHU hU) hzero (hSU hU)
      refine ⟨g, K, hK, fun _ ↦ hKU, ?_, ?_, fun _ ↦ hg, ?_⟩
      · intro hV
        exact (hboth ⟨hU, hV⟩).elim
      · intro hcap
        exact (hboth ⟨fun s ↦ (hcap s).1, fun s ↦ (hcap s).2⟩).elim
      · intro hV
        exact (hboth ⟨hU, hV⟩).elim
    · obtain ⟨g, K, hK, hKV, hg⟩ := exists_face_subspace_normalization F V U c e hce q hVU
        f hV H (hHV hV) hzero (hSV hV)
      refine ⟨g, K, hK, ?_, fun _ ↦ hKV, ?_, ?_, fun _ ↦ hg⟩
      · intro hU
        exact (hboth ⟨hU, hV⟩).elim
      · intro hcap
        exact (hboth ⟨fun s ↦ (hcap s).1, fun s ↦ (hcap s).2⟩).elim
      · intro hU
        exact (hboth ⟨hU, hV⟩).elim

end Topology.CubicalSubdivision
