/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Homotopy.Equiv

/-! # Homotopy equivalences of topological disjoint unions

Selected from `Quillen/Topology/Realization/Coproduct.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual component maps and homotopies
are unchanged; no compatibility between different components is required.
-/
@[expose] public noncomputable section
universe u
namespace ContinuousMap
variable {ι : Type u}

/-- A family of continuous maps acts continuously on the topological disjoint union. -/
def sigmaContinuousMap {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(X i, Y i)) : C((Σ i, X i), Σ i, Y i) :=
  ContinuousMap.sigma fun i ↦ (ContinuousMap.sigmaMk i).comp (f i)

/-- A family of homotopies acts continuously on the topological disjoint union. -/
def sigmaHomotopy {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f g : ∀ i, C(X i, Y i)}
    (h : ∀ i, (f i).Homotopy (g i)) :
    (ContinuousMap.sigmaContinuousMap f).Homotopy (ContinuousMap.sigmaContinuousMap g) where
  toFun z := ⟨z.2.1, h z.2.1 (z.1, z.2.2)⟩
  continuous_toFun := by
    let e : (unitInterval × Σ i, X i) ≃ₜ Σ i, X i × unitInterval :=
      (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
    have hc : Continuous (fun z : (Σ i, X i × unitInterval) ↦
        (⟨z.1, h z.1 (z.2.2, z.2.1)⟩ : Σ i, Y i)) :=
      continuous_sigma fun i ↦ continuous_sigmaMk.comp
        ((h i).continuous.comp (continuous_snd.prodMk continuous_fst))
    exact hc.comp e.continuous
  map_zero_left x := by cases x; simp [ContinuousMap.sigmaContinuousMap]
  map_one_left x := by cases x; simp [ContinuousMap.sigmaContinuousMap]

/-- Homotopy equivalences assemble over a disjoint union, without any coherence
conditions between distinct components. -/
def sigmaHomotopyEquiv {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap.HomotopyEquiv (Σ i, X i) (Σ i, Y i) where
  toFun := ContinuousMap.sigmaContinuousMap fun i ↦ (e i).toFun
  invFun := ContinuousMap.sigmaContinuousMap fun i ↦ (e i).invFun
  left_inv := ⟨ContinuousMap.sigmaHomotopy fun i ↦ (e i).left_inv.some⟩
  right_inv := ⟨ContinuousMap.sigmaHomotopy fun i ↦ (e i).right_inv.some⟩

end ContinuousMap
