/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.FiniteSubdivision

/-!
# Refinement

Endpoint transport of the actual path is exactly transport of its normalized
local arrow; arbitrary objects of the target are never identified implicitly.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Set
universe u v w z
namespace FundamentalGroupoid.OpenCover.ChartData
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C] {U : ι → Set X}
variable (d : ChartData (C := C) U)

/-- Endpoint transport of the actual path is exactly transport of its normalized
local arrow; arbitrary objects of the target are never identified implicitly. -/
theorem localValue_cast (i : ι) {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) (hp : Set.range p ⊆ U i)
    (hc : Set.range (p.cast hx hy) ⊆ U i) :
    d.localValue i (p.cast hx hy) hc =
      eqToHom (congrArg d.obj hx) ≫ d.localValue i p hp ≫
        eqToHom (congrArg d.obj hy.symm) := by
  subst x'
  subst y'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Path.cast_rfl_rfl]

/-- A finite subdivision of one actual local path can use different charts on
every fine edge. After the explicit endpoint transports its ordered value is
the original local value. Covering and finiteness are supplied by these actual
containment proofs and Fin-indexed data, not by a global evaluator. -/
theorem localValue_refinement (hc : d.Compatible) (i : ι) {x y : X}
    (p : Path x y) (hp : Set.range p ⊆ U i) {n : ℕ}
    (t : Fin (n + 1) → unitInterval) (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (k : Fin n → ι)
    (hk : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (k j)) :
    eqToHom (congrArg d.obj ((congrArg p ht0).trans p.source).symm) ≫
      finiteChainComp (fun j => d.obj (p (t j)))
        (fun j => d.localValue (k j) (p.subpath (t j.castSucc) (t j.succ)) (hk j)) ≫
      eqToHom (congrArg d.obj ((congrArg p ht1).trans p.target)) =
        d.localValue i p hp := by
  rw [d.finiteValue_chart_independent hc (fun j => p (t j))
    (fun j => p.subpath (t j.castSucc) (t j.succ)) k (fun _ => i) hk
    (fun j => subpath_contained i p hp (t j.castSucc) (t j.succ))]
  rw [d.localValue_finiteSubdivision i p hp t]
  let h0 : p (t 0) = x := (congrArg p ht0).trans p.source
  let h1 : p (t (Fin.last n)) = y := (congrArg p ht1).trans p.target
  have hq : (p.subpath (t 0) (t (Fin.last n))).cast h0.symm h1.symm = p := by
    ext s
    simp [Path.subpath, ht0, ht1]
  have hh : Set.range ((p.subpath (t 0) (t (Fin.last n))).cast h0.symm h1.symm) ⊆ U i := by
    rw [hq]
    exact hp
  have he := d.localValue_cast i (p.subpath (t 0) (t (Fin.last n))) h0.symm h1.symm
    (subpath_contained i p hp (t 0) (t (Fin.last n))) hh
  simpa only [hq] using he.symm

end FundamentalGroupoid.OpenCover.ChartData
