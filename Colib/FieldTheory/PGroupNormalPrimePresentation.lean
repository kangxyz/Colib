/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.PGroupNormalSubfieldEmbedding
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# A normal prime polynomial presentation inside the original field

The native primitive-element power basis presents an actual normal prime
subfield of the original field. Its minimal polynomial is returned literally,
together with monicity and irreducibility, rather than in a separate polynomial
presentation type. The algebra embedding lands in the original field.

The characteristic-zero scope of the source theorem is retained.
-/

@[expose] public noncomputable section

namespace Field

open Polynomial

variable {k H Ω : Type*} [Field k] [Field H] [Field Ω]
  [Algebra k H] [Algebra k Ω] [FiniteDimensional k H]
  [FiniteDimensional k Ω] [IsGalois k Ω] [CharZero k]

/-- A nontrivial finite field extension embedded in a finite Galois `p`-group extension
contains the root field of a literal monic irreducible normal degree-`p`
polynomial. The specified embedding has codomain the original field `H`. -/
@[colib_tag "COL-0221",
  colib_ref "aglib_principal_euler_pin" "KTheory/MilnorK/PGroupNormalPrimePresentation.lean:33-52"
    "adaptation"
    "Literal minimal polynomial and native root-field embedding into H; CharZero retained"]
theorem exists_normal_prime_presentation_of_isPGroup_embedding
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (Ω ≃ₐ[k] Ω))
    (g : H →ₐ[k] Ω) (hH : 1 < Module.finrank k H) :
    ∃ r : k[X], r.Monic ∧ ∃ hr : Irreducible r,
      let _ : Fact (Irreducible r) := ⟨hr⟩
      Normal k (AdjoinRoot r) ∧ r.natDegree = p ∧
        Nonempty (AdjoinRoot r →ₐ[k] H) := by
  obtain ⟨L, hnormal, hdegree, _⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_embedding p hG g hH
  let : Normal k L := hnormal
  let pb : PowerBasis k L := powerBasisOfFiniteOfSeparable k L
  let r : k[X] := minpoly k pb.gen
  have hr : Irreducible r := minpoly.irreducible pb.isIntegral_gen
  let : Fact (Irreducible r) := ⟨hr⟩
  let ε : AdjoinRoot r ≃ₐ[k] L := AdjoinRoot.equiv' r pb
    (by
      change aeval (AdjoinRoot.root r) r = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
    (minpoly.aeval k pb.gen)
  refine ⟨r, minpoly.monic pb.isIntegral_gen, hr,
    Normal.of_algEquiv ε.symm, ?_, ⟨L.val.comp ε.toAlgHom⟩⟩
  change (minpoly k pb.gen).natDegree = p
  rw [pb.natDegree_minpoly, ← pb.finrank, hdegree]

end Field
