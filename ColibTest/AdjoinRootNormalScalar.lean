/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.AdjoinRoot.NormalScalar

/-!
# Consumers of actual scalar-factor splitting fields

These consumers have no characteristic, separability, prime-degree, or finite
coefficient-extension assumption. Normality and minimal-polynomial splitting
come directly from the native splitting-field API.
-/

noncomputable section

namespace ColibTest.AdjoinRootNormalScalar

open Polynomial

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
  {p : k[X]} [Fact (Irreducible p)] [Normal k (AdjoinRoot p)]

/-- The whole coefficient image splits in every actual irreducible factor's
root field, even when the coefficient extension is not finite. -/
theorem actual_factor_splitting_field (hp : p.Monic) (q : L[X])
    [Fact (Irreducible q)] (hd : q ∣ p.map (algebraMap k L)) :
    IsSplittingField L (AdjoinRoot q) (p.map (algebraMap k L)) :=
  AdjoinRoot.isSplittingField_of_dvd_map hp hd

/-- Native normality is obtained without a second compatibility theorem. -/
theorem actual_factor_normal (hp : p.Monic) (q : L[X])
    [Fact (Irreducible q)] (hd : q ∣ p.map (algebraMap k L)) :
    Normal L (AdjoinRoot q) := by
  let : IsSplittingField L (AdjoinRoot q) (p.map (algebraMap k L)) :=
    AdjoinRoot.isSplittingField_of_dvd_map hp hd
  exact Normal.of_isSplittingField (p.map (algebraMap k L))

/-- An irreducible whole coefficient image is a valid literal factor. -/
theorem whole_coefficient_image_normal (hp : p.Monic)
    [Fact (Irreducible (p.map (algebraMap k L)))] :
    Normal L (AdjoinRoot (p.map (algebraMap k L))) := by
  let : IsSplittingField L (AdjoinRoot (p.map (algebraMap k L)))
      (p.map (algebraMap k L)) := AdjoinRoot.isSplittingField_of_dvd_map hp dvd_rfl
  exact Normal.of_isSplittingField (p.map (algebraMap k L))

/-- Consumers get normality of the literal quotient field and hence splitting
of each of its actual minimal polynomials. -/
theorem actual_factor_minpoly_splits (hp : p.Monic) (q : L[X])
    [Fact (Irreducible q)] (hd : q ∣ p.map (algebraMap k L))
    (x : AdjoinRoot q) : ((minpoly L x).map (algebraMap L (AdjoinRoot q))).Splits := by
  let : IsSplittingField L (AdjoinRoot q) (p.map (algebraMap k L)) :=
    AdjoinRoot.isSplittingField_of_dvd_map hp hd
  let : Normal L (AdjoinRoot q) := Normal.of_isSplittingField (p.map (algebraMap k L))
  exact Normal.splits (inferInstance : Normal L (AdjoinRoot q)) x

/-- Taking the coefficient field to be the original field recovers splitting
in the literal original root field. -/
theorem original_root_field_splits (hp : p.Monic) :
    (p.map (algebraMap k (AdjoinRoot p))).Splits := by
  let : IsSplittingField k (AdjoinRoot p) (p.map (algebraMap k k)) :=
    AdjoinRoot.isSplittingField_of_dvd_map hp (by simp)
  simpa using IsSplittingField.splits (AdjoinRoot p) (p.map (algebraMap k k))

/-- After extension to the original root field every actual irreducible
factor is linear, in arbitrary characteristic. -/
theorem root_field_factor_linear (hp : p.Monic) {q : (AdjoinRoot p)[X]}
    (hq : Irreducible q) (hd : q ∣ p.map (algebraMap k (AdjoinRoot p))) :
    q.natDegree = 1 := by
  have hsplit := original_root_field_splits hp
  exact (hsplit.of_dvd (map_ne_zero hp.ne_zero) hd).natDegree_eq_one_of_irreducible hq

end ColibTest.AdjoinRootNormalScalar
