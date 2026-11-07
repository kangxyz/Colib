/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.HomotopyInvariance

/-!
# Ambient Value

Any two subordinate path subdivisions have equal values along a genuinely
subordinate endpoint-fixed ambient homotopy grid. No global decoder is assumed.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
variable {C : Type w} [Category.{z} C]

/-- Any two subordinate path subdivisions have equal values along a genuinely
subordinate endpoint-fixed ambient homotopy grid. No global decoder is assumed. -/
theorem PathSubdivision.value_eq_of_homotopySubdivision {x y : X} {p q : Path x y}
    (s : PathSubdivision (U := U) p) (t : PathSubdivision (U := U) q)
    (H : p.Homotopy q) (g : HomotopySubdivision (U := U) H)
    (d : ChartData (C := C) U) (hc : d.Compatible)
    (hcover : Set.range H ⊆ ⋃ i, U i) : s.value d = t.value d := by
  classical
  choose ih hh using g.horizontal_chart
  have hp : H.eval (g.times 0) = p := by
    ext a
    change H (g.times 0, a) = p a
    rw [g.first]
    exact H.map_zero_left a
  have hq : H.eval (g.times (Fin.last g.n)) = q := by
    ext a
    change H (g.times (Fin.last g.n), a) = q a
    rw [g.last]
    exact H.map_one_left a
  have cp : Set.range p ⊆ ⋃ i, U i := by
    rintro _ ⟨a, rfl⟩
    exact (H.map_zero_left a) ▸ hcover (Set.mem_range_self (0, a))
  have cq : Set.range q ⊆ ⋃ i, U i := by
    rintro _ ⟨a, rfl⟩
    exact (H.map_one_left a) ▸ hcover (Set.mem_range_self (1, a))
  obtain ⟨kx, hx⟩ := Set.mem_iUnion.mp (cp p.source_mem_range)
  obtain ⟨ky, hy⟩ := Set.mem_iUnion.mp (cq q.target_mem_range)
  calc
    s.value d = (g.row 0 (ih 0) (hh 0)).value d :=
      s.value_eq_of_path_eq _ hp.symm d hc cp
    _ = (g.row (Fin.last g.n) (ih (Fin.last g.n)) (hh (Fin.last g.n))).value d :=
      g.row_value_eq d hc ih hh kx ky hx hy
    _ = t.value d :=
      PathSubdivision.value_eq_of_path_eq _ t hq d hc (hq.symm ▸ cq)

/-- Actual ambient endpoint-fixed homotopy invariance of the ordered local value.
Compactness supplies the finite grid from an open cover of the homotopy image;
chart functors must agree on every actual overlap path. -/
theorem PathSubdivision.value_eq_of_homotopy {x y : X} {p q : Path x y}
    (s : PathSubdivision (U := U) p) (t : PathSubdivision (U := U) q)
    (H : p.Homotopy q) (d : ChartData (C := C) U) (hc : d.Compatible)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.range H ⊆ ⋃ i, U i) :
    s.value d = t.value d := by
  obtain ⟨g⟩ := homotopySubdivision_nonempty H U hU hcover
  exact s.value_eq_of_homotopySubdivision t H g d hc hcover

end FundamentalGroupoid.OpenCover
