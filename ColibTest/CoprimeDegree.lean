/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.Polynomial.CoprimeDegree
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Coprime-degree coefficient extensions without separability

The coefficient fields have independent universes. All results concern the
literal coefficient image and its actual factors and root field. Perfectness,
characteristic zero, normality, and Galoisness are not assumptions.
-/

noncomputable section

namespace ColibTest.CoprimeDegree

open Polynomial

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L]

/-- The whole image stays irreducible for an arbitrary finite coefficient
extension of coprime degree, in an independent universe. -/
theorem actual_irreducibility (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L)) :
    Irreducible (p.map (algebraMap k L)) :=
  hp.irreducible_map_of_natDegree_coprime hirr hcop

/-- Every literal irreducible factor has degree divisible by the original
degree, without a monicity assumption on the factor. -/
theorem actual_factor_degree (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L))
    (q : L[X]) (hq : Irreducible q) (hdiv : q ∣ p.map (algebraMap k L)) :
    p.natDegree ∣ q.natDegree :=
  natDegree_dvd_of_irreducible_factor_of_coprime hp hirr hcop hq hdiv

/-- Native associatedness upgrades divisibility to exact factor degree.
The actual factor still need not be monic. -/
theorem actual_factor_degree_eq (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L))
    (q : L[X]) (hq : Irreducible q) (hdiv : q ∣ p.map (algebraMap k L)) :
    q.natDegree = p.natDegree := by
  have hmap := hp.irreducible_map_of_natDegree_coprime hirr hcop
  have hdegree := natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (hq.associated_of_dvd hmap hdiv))
  simpa only [Polynomial.natDegree_map] using hdegree

/-- Equality with the literal coefficient image uses the factor's monicity,
unlike equality of degrees. -/
theorem monic_factor_eq (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L))
    (q : L[X]) (hqm : q.Monic) (hqi : Irreducible q)
    (hdiv : q ∣ p.map (algebraMap k L)) : q = p.map (algebraMap k L) := by
  have hmap := hp.irreducible_map_of_natDegree_coprime hirr hcop
  exact eq_of_monic_of_associated hqm (hp.map _) (hqi.associated_of_dvd hmap hdiv)

/-- The literal image's native root field has exactly the original degree;
no replacement factor or separately packaged field is introduced. -/
theorem mapped_root_field_degree (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L)) :
    let hmap := hp.irreducible_map_of_natDegree_coprime hirr hcop
    let _ : Fact (Irreducible (p.map (algebraMap k L))) := ⟨hmap⟩
    Module.finrank L (AdjoinRoot (p.map (algebraMap k L))) = p.natDegree := by
  let hmap := hp.irreducible_map_of_natDegree_coprime hirr hcop
  let : Fact (Irreducible (p.map (algebraMap k L))) := ⟨hmap⟩
  dsimp only
  rw [(AdjoinRoot.powerBasis hmap.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    Polynomial.natDegree_map]

/-- Linear polynomials meet the ordinary coprimality premise in every finite
coefficient extension. -/
theorem linear_polynomial (a : k) :
    Irreducible ((X - C a).map (algebraMap k L)) :=
  (monic_X_sub_C a).irreducible_map_of_natDegree_coprime (irreducible_X_sub_C a)
    (by rw [natDegree_X_sub_C]; exact Nat.coprime_one_left _)

/-- For prime-degree polynomials it is enough that the prime not divide the
finite coefficient-extension degree. -/
theorem prime_degree (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hprime : p.natDegree.Prime) (hdegree : ¬p.natDegree ∣ Module.finrank k L) :
    Irreducible (p.map (algebraMap k L)) :=
  hp.irreducible_map_of_natDegree_coprime hirr (hprime.coprime_iff_not_dvd.mpr hdegree)

/-- Purely inseparable finite coefficient extensions are included. The
explicit unused instance records this regression context; the theorem used
does not need a separability or perfect-base premise. -/
theorem purely_inseparable_coefficients [_purelyInseparable : IsPurelyInseparable k L]
    (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L)) :
    Irreducible (p.map (algebraMap k L)) :=
  hp.irreducible_map_of_natDegree_coprime hirr hcop

end ColibTest.CoprimeDegree
