/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

import Colib.Analysis.Convex.StdSimplex.FaceCharts

/-!
# Native simplex face-coordinate regression tests

The omitted face coordinate theorem retains its native simplex-map statement,
its definitionally equal finite-support coordinate, and the face-overlap rewrite.
-/

open Convexity

example {d : ℕ} (i : Fin (d + 2)) (x : StdSimplex ℝ (Fin (d + 1))) :
    (x.map i.succAbove).weights i = 0 :=
  StdSimplex.map_succAbove_self i x

example {d : ℕ} (i : Fin (d + 2)) (x : StdSimplex ℝ (Fin (d + 1))) :
    (Finsupp.mapDomain i.succAbove x.weights) i = 0 :=
  StdSimplex.map_succAbove_self i x

example (d : ℕ) (i : Fin (d + 3)) (k : Fin (d + 2))
    (x y : StdSimplex ℝ (Fin (d + 2)))
    (h : x.map i.succAbove = y.map (i.succAbove k).succAbove) :
    x.weights k = 0 := by
  have hz := StdSimplex.map_succAbove_self (i.succAbove k) y
  rw [← h, StdSimplex.map_apply_injective Fin.succAbove_right_injective] at hz
  exact hz
