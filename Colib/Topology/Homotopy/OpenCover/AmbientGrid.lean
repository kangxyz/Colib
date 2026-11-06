/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.Subordinate

/-!
# Ambient Grid

Actual ambient-homotopy cells paste for any independently chosen subordinate
edge charts. This is the four-sided grid equation, before fixed-endpoint transport.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
variable {C : Type w} [Category.{z} C]

/-- Actual ambient-homotopy cells paste for any independently chosen subordinate
edge charts. This is the four-sided grid equation, before fixed-endpoint transport. -/
theorem HomotopySubdivision.commSq {x y : X} {p q : Path x y} {H : p.Homotopy q}
    (g : HomotopySubdivision (U := U) H) (d : ChartData (C := C) U) (hc : d.Compatible)
    (ih : Fin (g.n + 1) → Fin g.n → ι) (iv : Fin g.n → Fin (g.n + 1) → ι)
    (hh : ∀ i j, Set.range ((H.eval (g.times i)).subpath
      (g.times j.castSucc) (g.times j.succ)) ⊆ U (ih i j))
    (hv : ∀ i j, Set.range ((homotopyColumn H (g.times j)).subpath
      (g.times i.castSucc) (g.times i.succ)) ⊆ U (iv i j)) :
    CommSq
      (finiteChainComp (fun j => d.obj (H (g.times 0, g.times j)))
        (fun j => d.localValue (ih 0 j) ((H.eval (g.times 0)).subpath
          (g.times j.castSucc) (g.times j.succ)) (hh 0 j)))
      (finiteChainComp (fun i => d.obj (H (g.times i, g.times 0)))
        (fun i => d.localValue (iv i 0) ((homotopyColumn H (g.times 0)).subpath
          (g.times i.castSucc) (g.times i.succ)) (hv i 0)))
      (finiteChainComp (fun i => d.obj (H (g.times i, g.times (Fin.last g.n))))
        (fun i => d.localValue (iv i (Fin.last g.n))
          ((homotopyColumn H (g.times (Fin.last g.n))).subpath
          (g.times i.castSucc) (g.times i.succ)) (hv i (Fin.last g.n))))
      (finiteChainComp (fun j => d.obj (H (g.times (Fin.last g.n), g.times j)))
        (fun j => d.localValue (ih (Fin.last g.n) j)
          ((H.eval (g.times (Fin.last g.n))).subpath
          (g.times j.castSucc) (g.times j.succ)) (hh (Fin.last g.n) j))) :=
  d.finiteGrid_localValue hc (fun i j => H (g.times i, g.times j))
    (fun i j => (H.eval (g.times i)).subpath (g.times j.castSucc) (g.times j.succ))
    (fun i j => (homotopyColumn H (g.times j)).subpath (g.times i.castSucc) (g.times i.succ))
    ih iv hh hv g.filling

end FundamentalGroupoid.OpenCover
