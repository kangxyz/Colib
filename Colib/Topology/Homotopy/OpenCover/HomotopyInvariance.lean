/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.GridBoundary

/-!
# Homotopy Invariance

A genuinely chart-subordinate ambient homotopy equates its normalized boundary
row values. The two other boundary chains are constant by endpoint-fixedness.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
variable {C : Type w} [Category.{z} C]

/-- A genuinely chart-subordinate ambient homotopy equates its normalized boundary
row values. The two other boundary chains are constant by endpoint-fixedness. -/
theorem HomotopySubdivision.row_value_eq {x y : X} {p q : Path x y} {H : p.Homotopy q}
    (g : HomotopySubdivision (U := U) H) (d : ChartData (C := C) U) (hc : d.Compatible)
    (ih : Fin (g.n + 1) → Fin g.n → ι)
    (hh : ∀ i j, Set.range ((H.eval (g.times i)).subpath
      (g.times j.castSucc) (g.times j.succ)) ⊆ U (ih i j))
    (kx ky : ι) (hx : x ∈ U kx) (hy : y ∈ U ky) :
    (g.row 0 (ih 0) (hh 0)).value d =
      (g.row (Fin.last g.n) (ih (Fin.last g.n)) (hh (Fin.last g.n))).value d := by
  classical
  choose iv hv using g.vertical_chart
  have sq := (g.commSq d hc ih iv hh hv).w
  have el (i : Fin (g.n + 1)) : H (g.times i, g.times 0) = x := by
    rw [g.first]
    exact H.source _
  have er (i : Fin (g.n + 1)) : H (g.times i, g.times (Fin.last g.n)) = y := by
    rw [g.last]
    exact H.target _
  have hl := d.finiteConstantValue hc (fun i => H (g.times i, g.times 0)) x el
    (fun i => (homotopyColumn H (g.times 0)).subpath (g.times i.castSucc) (g.times i.succ))
    (by intro i t; change H (_, g.times 0) = x; rw [g.first]; exact H.source _)
    (fun i => iv i 0) (fun i => hv i 0) kx hx
  have hr := d.finiteConstantValue hc (fun i => H (g.times i, g.times (Fin.last g.n))) y er
    (fun i => (homotopyColumn H (g.times (Fin.last g.n))).subpath
      (g.times i.castSucc) (g.times i.succ))
    (by intro i t; change H (_, g.times (Fin.last g.n)) = y; rw [g.last]; exact H.target _)
    (fun i => iv i (Fin.last g.n)) (fun i => hv i (Fin.last g.n)) ky hy
  have he := congrArg (fun f => eqToHom (congrArg d.obj (el 0).symm) ≫ f ≫
    eqToHom (congrArg d.obj (er (Fin.last g.n)))) sq
  rw [hl, hr] at he
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id, Category.id_comp, HomotopySubdivision.row, PathSubdivision.value,
      Path.Homotopy.eval, Path.coe_mk_mk, ContinuousMap.Homotopy.curry_apply,
      ContinuousMap.HomotopyWith.coe_toHomotopy] using he

end FundamentalGroupoid.OpenCover
