/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.JoinValue

/-!
# Descent

Actual path concatenation is sent to composition, by a genuine joined
subdivision and the proved independence of subdivision and chart choices.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover.ChartData
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
variable {C : Type w} [Category.{z} C]
variable (d : ChartData (C := C) U) (c : CoverData U) (hc : d.Compatible)
include hc

/-- Actual path concatenation is sent to composition, by a genuine joined
subdivision and the proved independence of subdivision and chart choices. -/
theorem pathValue_trans {x y z : X} (p : Path x y) (q : Path y z) :
    d.pathValue c (p.trans q) = d.pathValue c p ≫ d.pathValue c q := by
  rw [d.pathValue_eq c hc _ ((c.subdivision p).join (c.subdivision q))]
  exact (c.subdivision p).join_value (c.subdivision q) d hc

/-- The global descent functor constructed from actual compatible chart functors.
No global decoder, retraction or inverse comparison is assumed as input. -/
def descent : FundamentalGroupoid X ⥤ C where
  obj x := d.obj x.as
  map f := d.quotientValue c hc f
  map_id x := d.pathValue_refl c hc x.as
  map_comp f g := by
    induction f using _root_.Quotient.ind with | _ p =>
      induction g using _root_.Quotient.ind with | _ q =>
        exact d.pathValue_trans c hc p q

/-- Exact local recovery on each actual chart-contained ambient path. -/
theorem descent_local {x y : X} (p : Path x y) (i : ι)
    (hp : Set.range p ⊆ U i) :
    (d.descent c hc).map (show FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y from
      Path.Homotopic.Quotient.mk p) = d.localValue i p hp :=
  d.pathValue_local c hc i p hp

end FundamentalGroupoid.OpenCover.ChartData
