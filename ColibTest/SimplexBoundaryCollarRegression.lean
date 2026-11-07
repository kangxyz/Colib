/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Realization.SimplexBoundaryCollar

/-! Actual radial coordinates and relative collar homotopy regression tests.
No HEP statement or transport to simplicial realization is asserted. -/
@[expose] public noncomputable section
open scoped unitInterval Topology
namespace Convexity.StdSimplex

example {n : ℕ} (z : Convexity.StdSimplex ℝ (Fin (n + 1)) × I) (i : Fin (n + 1)) :
    (simplexBoundaryRetractPoint z).weights i =
      ((n + 1 : ℝ) * z.1.weights i + simplexBoundaryScale z - 1) /
        ((n + 1 : ℝ) * simplexBoundaryScale z) := rfl

example {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryRetractPoint (x, 0) = x := simplexBoundaryRetractPoint_zero x

example {n : ℕ} (x : boundary n) (t : I) :
    simplexBoundaryRetractPoint (x.1, t) = x.1 := simplexBoundaryRetractPoint_boundary x t

example {n : ℕ} (x : simplexBoundaryCollar n) (t : I) :
    simplexBoundaryRetractPoint (x.1, t) ∈ simplexBoundaryCollar n :=
  simplexBoundaryRetractPoint_mem_collar x t

example {n : ℕ} (x : simplexBoundaryCollar n) :
    (simplexBoundaryCollarRetraction n x).1 = simplexBoundaryRetractPoint (x.1, 1) := rfl

example (n : ℕ) : (simplexBoundaryCollarHomotopyEquiv n).toFun =
    simplexBoundaryCollarInclusion n := rfl

example (n : ℕ) : IsOpen (simplexBoundaryCollar n) := isOpen_simplexBoundaryCollar n

example (z : Convexity.StdSimplex ℝ (Fin 1) × I) :
    simplexBoundaryRetract z ∈ simplexBoundaryCylinder 0 := simplexBoundaryRetract_mem z

example (x : boundary 0) (t : I) :
    simplexBoundaryRetractPoint (x.1, t) = x.1 := simplexBoundaryRetractPoint_boundary x t

end Convexity.StdSimplex


namespace Convexity.StdSimplex

example {n : ℕ} (z : Convexity.StdSimplex ℝ (Fin (n + 1)) × I) :
    simplexBoundaryScale z = max (1 - (z.2 : ℝ) / 2) (simplexBoundaryDefect z.1) := rfl

example {n : ℕ} (z : Convexity.StdSimplex ℝ (Fin (n + 1)) × I) :
    ((simplexBoundaryRetract z).2 : ℝ) =
      2 + ((z.2 : ℝ) - 2) / simplexBoundaryScale z := rfl

example {n : ℕ} (z : Convexity.StdSimplex ℝ (Fin (n + 1)) × I)
    (hz : z ∈ simplexBoundaryCylinder n) : simplexBoundaryRetract z = z :=
  simplexBoundaryRetract_eq_self z hz

example {n : ℕ} (x : boundary n) (t : I) :
    simplexBoundaryRetract (x.1, t) = (x.1, t) :=
  simplexBoundaryRetract_eq_self _ (Or.inl x.2)

example {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryRetract (x, 0) = (x, 0) :=
  simplexBoundaryRetract_eq_self _ (Or.inr rfl)

example (n : ℕ) : Continuous (simplexBoundaryRetract (n := n)) :=
  continuous_simplexBoundaryRetract

example (n : ℕ) : boundary n ⊆ simplexBoundaryCollar n :=
  simplexBoundary_subset_collar n

example {n : ℕ} (x : simplexBoundaryCollar n) (t : I) :
    (simplexBoundaryCollarHomotopy n (t, x)).1 =
      simplexBoundaryRetractPoint (x.1, t) := rfl

example {n : ℕ} (x : boundary n) (t : I) :
    simplexBoundaryCollarHomotopy n (t, simplexBoundaryCollarInclusion n x) =
      simplexBoundaryCollarInclusion n x := by
  apply Subtype.ext
  exact simplexBoundaryRetractPoint_boundary x t

example (n : ℕ) : (simplexBoundaryCollarHomotopyEquiv n).invFun =
    simplexBoundaryCollarRetraction n := rfl

example (n : ℕ) (x : boundary n) :
    simplexBoundaryCollarRetraction n (simplexBoundaryCollarInclusion n x) = x :=
  simplexBoundaryCollarRetraction_inclusion n x

example : ContinuousMap.HomotopyEquiv (boundary 0) (simplexBoundaryCollar 0) :=
  simplexBoundaryCollarHomotopyEquiv 0

end Convexity.StdSimplex
