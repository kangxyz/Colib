/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.AmbientGrid
public import Colib.Topology.Homotopy.OpenCover.PathTransport

/-!
# Grid Boundary

A horizontal grid row is an actual subordinate path subdivision.
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

/-- A horizontal grid row is an actual subordinate path subdivision. -/
def HomotopySubdivision.row {x y : X} {p q : Path x y} {H : p.Homotopy q}
    (g : HomotopySubdivision (U := U) H) (i : Fin (g.n + 1))
    (k : Fin g.n → ι)
    (hk : ∀ j, Set.range ((H.eval (g.times i)).subpath
      (g.times j.castSucc) (g.times j.succ)) ⊆ U (k j)) :
    PathSubdivision (U := U) (H.eval (g.times i)) :=
  ⟨g.n, g.times, g.monotone, g.first, g.last, k, hk⟩

/-- Equal actual paths may use unrelated finite subdivisions and chart choices. -/
theorem PathSubdivision.value_eq_of_path_eq {x y : X} {p q : Path x y}
    (s : PathSubdivision (U := U) p) (t : PathSubdivision (U := U) q)
    (h : p = q) (d : ChartData (C := C) U) (hc : d.Compatible)
    (hcover : Set.range p ⊆ ⋃ i, U i) : s.value d = t.value d := by
  subst q
  exact s.value_eq t d hc hcover

/-- A finite chain of actual constant paths has just its endpoint transport. -/
theorem ChartData.finiteConstantValue (d : ChartData (C := C) U) (hc : d.Compatible)
    {n : ℕ} (a : Fin (n + 1) → X) (x : X) (e : ∀ j, a j = x)
    (p : ∀ j : Fin n, Path (a j.castSucc) (a j.succ)) (he : ∀ j t, p j t = x)
    (i : Fin n → ι) (hi : ∀ j, Set.range (p j) ⊆ U (i j))
    (k : ι) (hx : x ∈ U k) :
    finiteChainComp (fun j => d.obj (a j)) (fun j => d.localValue (i j) (p j) (hi j)) =
      eqToHom (congrArg d.obj (e 0)) ≫ eqToHom (congrArg d.obj (e (Fin.last n)).symm) := by
  have hk : Set.range (Path.refl x) ⊆ U k := by rintro _ ⟨t, rfl⟩; exact hx
  have h := d.finitePathValue_transport hc a (fun _ => x) e p (fun _ => Path.refl x)
    he i (fun _ => k) hi (fun _ => hk)
  simpa only [d.localValue_refl, finiteChainComp_id, Category.id_comp] using h

end FundamentalGroupoid.OpenCover
