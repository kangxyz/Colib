/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.Topology.MetricOrderComplex.RealizationCover

/-! # Regression checks for native metric order-complex covers -/

noncomputable section
open CategoryTheory SSet Opposite Topology Topology.MetricOrderComplex
open scoped Simplicial Topology
universe u

namespace ColibTest.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

example (x y : Topology.MetricOrderComplex P) :
    0 < commonMass x y ↔ dist x y < 2 :=
  commonMass_pos_iff_dist_lt_two x y

example (x : Topology.MetricOrderComplex P) :
    realizationCoordinates (realizationReconstruction x) = x :=
  realizationCoordinates_reconstruction x

example (p : P) :
    (realizationHomotopyEquiv (P := P)).toFun (classifyingSpacePoint p) = vertex p :=
  realizationCoordinates_vertex p

example (p : P) :
    (realizationHomotopyEquiv (P := P)).invFun (vertex p) = classifyingSpacePoint p :=
  cutoffRealizationMap_vertex p

example (p : P) (t : unitInterval) :
    (basedRealizationHomotopyEquiv p).leftHomotopy (t, classifyingSpacePoint p) =
      classifyingSpacePoint p :=
  (basedRealizationHomotopyEquiv p).left_fixed t

example {n m : SimplexCategory} (a : n ⟶ m) (s : (nerve P).obj (op m))
    (t : _root_.stdSimplex ℝ (Fin (n.len + 1))) :
    realizationCoordinates (realizationSimplex s (_root_.stdSimplex.map a t)) =
      simplexCoordinates ((nerve P).map a.op s) t := by
  rw [realizationCoordinates_simplex, simplexCoordinates_naturality]

example [PathConnectedSpace |nerve P|] (p : P) :
    ∃ T : Type u, ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, |nerve P|),
        IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T :=
  exists_simplyConnected_realization_cover p

end ColibTest.MetricOrderComplex
