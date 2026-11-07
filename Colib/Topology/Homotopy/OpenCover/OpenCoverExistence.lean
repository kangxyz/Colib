/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.Subdivision
public import Colib.Topology.Homotopy.OpenCover

/-!
# Open Cover Existence

An open cover of the actual path image supplies a finite monotone,
chart-labelled subdivision. The family of charts itself need not be finite.
-/

@[expose] public section

noncomputable section
open Set
universe u v
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- An open cover of the actual path image supplies a finite monotone,
chart-labelled subdivision. The family of charts itself need not be finite. -/
theorem pathSubdivision_nonempty {x y : X} (p : Path x y)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.range p ⊆ ⋃ i, U i) : Nonempty (PathSubdivision (U := U) p) := by
  obtain ⟨n, t, h0, h1, hm, h⟩ := p.exists_subdivision_openCover U hU hcover
  choose chart hc using h
  exact ⟨⟨n, t, hm, h0, h1, chart, hc⟩⟩

end FundamentalGroupoid.OpenCover
