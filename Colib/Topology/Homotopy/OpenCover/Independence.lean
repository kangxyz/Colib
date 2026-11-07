/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.FiniteTransport

/-!
# Independence

Arbitrary finite subdivisions of the same actual path have equal values.
Every fine edge has its actual containing chart; overlap compatibility is used
on actual paths. A cover of the path image also handles constant max-grid edges
outside an original segment. No global decoder is an input.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Set
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C] {U : ι → Set X}

/-- Arbitrary finite subdivisions of the same actual path have equal values.
Every fine edge has its actual containing chart; overlap compatibility is used
on actual paths. A cover of the path image also handles constant max-grid edges
outside an original segment. No global decoder is an input. -/
theorem PathSubdivision.value_eq {x y : X} {p : Path x y}
    (s t : PathSubdivision (U := U) p) (d : ChartData (C := C) U)
    (hc : d.Compatible) (hcover : Set.range p ⊆ ⋃ i, U i) : s.value d = t.value d := by
  classical
  let P := fun i : Fin (s.n + 1) => fun j : Fin (t.n + 1) =>
    p (max (s.times i) (t.times j))
  let h := fun i => fun j : Fin t.n =>
    p.subpath (max (s.times i) (t.times j.castSucc)) (max (s.times i) (t.times j.succ))
  let v := fun i : Fin s.n => fun j =>
    p.subpath (max (s.times i.castSucc) (t.times j)) (max (s.times i.succ) (t.times j))
  have hex : ∀ (i : Fin (s.n + 1)) (j : Fin t.n), ∃ k, Set.range (h i j) ⊆ U k := by
    intro i j
    exact maxSubpath_exists_chart p hcover _ _ _ (t.monotone (Fin.castSucc_le_succ j))
      (t.chart j) (t.contained j)
  have vex : ∀ (i : Fin s.n) (j : Fin (t.n + 1)), ∃ k, Set.range (v i j) ⊆ U k := by
    intro i j
    obtain ⟨k, hk⟩ :=
      maxSubpath_exists_chart p hcover (s.times i.castSucc) (s.times i.succ) (t.times j)
        (s.monotone (Fin.castSucc_le_succ i)) (s.chart i) (s.contained i)
    refine ⟨k, ?_⟩
    change Set.range (p.subpath _ _) ⊆ U k
    rw [Path.range_subpath] at hk ⊢
    simpa only [max_comm (t.times j) (s.times i.castSucc),
      max_comm (t.times j) (s.times i.succ)] using hk
  choose ih hh using hex
  choose iv hv using vex
  have sq := (d.finiteGrid_localValue hc P h v ih iv hh hv (s.maxGridFilling t)).w
  have et : ∀ j, max (s.times 0) (t.times j) = t.times j := by
    intro j
    rw [s.first]
    exact max_eq_right unitInterval.nonneg'
  have es : ∀ i, max (s.times i) (t.times 0) = s.times i := by
    intro i
    rw [t.first]
    exact max_eq_left unitInterval.nonneg'
  have er : ∀ i, max (s.times i) (t.times (Fin.last t.n)) = (1 : unitInterval) := by
    intro i
    rw [t.last]
    exact max_eq_right unitInterval.le_one'
  have eb : ∀ j, max (s.times (Fin.last s.n)) (t.times j) = (1 : unitInterval) := by
    intro j
    rw [s.last]
    exact max_eq_left unitInterval.le_one'
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self (1 : unitInterval)))
  have hkpath : Set.range (p.subpath 1 1) ⊆ U k := by
    rw [Path.subpath_self]
    rintro _ ⟨r, rfl⟩
    exact hk
  have hid : d.localValue k (p.subpath 1 1) hkpath = 𝟙 (d.obj (p 1)) := by
    simpa only [Path.subpath_self] using d.localValue_refl k (p 1)
      (by rintro _ ⟨r, rfl⟩; exact hk)
  have htop := d.finiteSubpathValue_transport hc p _ t.times et
    (ih 0) t.chart (hh 0) t.contained
  have hleft := d.finiteSubpathValue_transport hc p _ s.times es
    (fun i => iv i 0) s.chart (fun i => hv i 0) s.contained
  have hright := d.finiteSubpathValue_transport hc p _ (fun _ : Fin (s.n + 1) => 1) er
    (fun i => iv i (Fin.last t.n)) (fun _ => k) (fun i => hv i (Fin.last t.n))
    (fun _ => hkpath)
  have hbottom := d.finiteSubpathValue_transport hc p _ (fun _ : Fin (t.n + 1) => 1) eb
    (ih (Fin.last s.n)) (fun _ => k) (hh (Fin.last s.n)) (fun _ => hkpath)
  simp only [hid, finiteChainComp_id, Category.id_comp] at hright hbottom
  have ea : P 0 0 = x := by
    dsimp [P]
    rw [s.first, t.first, max_self]
    exact p.source
  have ez : P (Fin.last s.n) (Fin.last t.n) = y := by
    dsimp [P]
    rw [s.last, t.last, max_self]
    exact p.target
  have he := congrArg (fun f => eqToHom (congrArg d.obj ea.symm) ≫ f ≫
    eqToHom (congrArg d.obj ez)) sq
  rw [htop, hright, hleft, hbottom] at he
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id, Category.id_comp, PathSubdivision.value] using he.symm

end FundamentalGroupoid.OpenCover
