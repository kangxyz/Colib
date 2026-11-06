/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.CategoryTheory.Groupoid.ConstantFunctor
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Overlap Loops

For an actual space, a condition on every actual based loop is enough to
trivialize its fundamental-groupoid functor along specified actual base paths.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X]
variable {C : Type w} [Category.{z} C]

/-- For an actual space, a condition on every actual based loop is enough to
trivialize its fundamental-groupoid functor along specified actual base paths. -/
def constantIsoOfActualLoops (F : FundamentalGroupoid X ⥤ C) (b : X)
    (α : ∀ x : X, Path x b)
    (hloop : ∀ p : Path b b, F.map (Path.Homotopic.Quotient.mk p) =
      𝟙 (F.obj (FundamentalGroupoid.mk b))) :
    F ≅ (Functor.const (FundamentalGroupoid X)).obj (F.obj (FundamentalGroupoid.mk b)) :=
  constantIsoOfLoopTrivial F (FundamentalGroupoid.mk b)
    (fun x => Path.Homotopic.Quotient.mk (α x.as)) (by
      intro f
      induction f using _root_.Quotient.ind with | _ p => exact hloop p)

/-- Simply connected actual overlaps discharge the loop condition for any
functor defined on their fundamental groupoid. This does not assert that the
two-dimensional attachment overlap is simply connected. -/
theorem map_actual_loop_eq_id [SimplyConnectedSpace X]
    (F : FundamentalGroupoid X ⥤ C) (b : X) (p : Path b b) :
    F.map (Path.Homotopic.Quotient.mk p) = 𝟙 (F.obj (FundamentalGroupoid.mk b)) := by
  have he : (Path.Homotopic.Quotient.mk p :
      FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b) =
        𝟙 (FundamentalGroupoid.mk b) := Subsingleton.elim _ _
  rw [he, F.map_id]

end FundamentalGroupoid.OpenCover
