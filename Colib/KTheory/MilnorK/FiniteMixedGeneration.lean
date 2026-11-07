/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.FiniteMixedWitnesses
public import Colib.FieldTheory.Polynomial.CoprimeDegree
public import Colib.FieldTheory.FiniteCoprimeSplitting

/-!
# Finite mixed generation in the same literal scalar extension

For each class in a prime-degree root field, choose its finite native reduced
representatives and one prime-to-degree intermediate field that splits them.
Coprime irreducibility keeps the whole original coefficient image irreducible.
The class then has a finite signed mixed-symbol expansion in precisely that
image's native root field, under precisely Mathlib's coefficient-factor map.

Perfectness is used by the finite simultaneous-splitting construction. The
lower mixed-symbol and finite-witness statements need neither perfectness,
characteristic zero, prime degree nor finite coefficient extensions.

This adapts `Aglib.KTheory.MilnorK.FiniteMixedGeneration`, lines 35-59, at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, retaining the actual intermediate field
and coefficient polynomial instead of introducing a presentation type.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial IntermediateField

universe u

variable {k : Type u} [Field k] [PerfectField k]

/-- A prime-degree root-field class has a finite signed mixed expansion after
one actual finite separable prime-to-degree coefficient extension. The target
polynomial is literally the original polynomial's coefficient image. -/
@[colib_tag "COL-0228",
  colib_ref "aglib_principal_euler_pin" "KTheory/MilnorK/FiniteMixedGeneration.lean:38-59"
    "adaptation"
    "Classwise finite mixed expansion over a perfect base, retaining prime degree"]
theorem exists_finite_coprime_milnorK_mixed_expansion (p : k[X]) (hp : p.Monic)
    [Fact (Irreducible p)] (hprime : p.natDegree.Prime) (m : ℕ)
    (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.natDegree) ∧
      ∃ S : IntermediateField k (∏ r ∈ s, r).SplittingField,
        FiniteDimensional k S ∧ Algebra.IsSeparable k S ∧
        p.natDegree.Coprime (Module.finrank k S) ∧
        (∀ r ∈ s, (r.map (algebraMap k S)).Splits) ∧
        ∃ hq : Irreducible (p.map (algebraMap k S)),
          let _ : Fact (Irreducible (p.map (algebraMap k S))) := ⟨hq⟩
          ∃ c : ((Fin m → Sˣ) × (AdjoinRoot (p.map (algebraMap k S)))ˣ) →₀ ℤ,
            (c.sum fun ab z => z • milnorKTupleSymbol
              (Fin.snoc (Units.map
                (algebraMap S (AdjoinRoot (p.map (algebraMap k S)))).toMonoidHom ∘ ab.1)
                ab.2)) =
              milnorKTheoryMap (AdjoinRoot.map (algebraMap k S) p
                (p.map (algebraMap k S)) dvd_rfl) (m + 1) x := by
  refine (exists_finite_milnorK_reduced_mixed_expansion.{u, u} p hp m x).elim ?_
  intro s hsgen
  have hs := hsgen.1
  have hgen := hsgen.2
  let : Fact p.natDegree.Prime := ⟨hprime⟩
  refine (exists_coprime_splitting_field_of_finset p.natDegree s
    (fun r hr => (hs r hr).1) (fun r hr => (hs r hr).2)).elim ?_
  intro S hS
  have hfinite := hS.1
  have hcop := hS.2.1
  have hsplit := hS.2.2
  let : FiniteDimensional k S := hfinite
  have hq : Irreducible (p.map (algebraMap k S)) :=
    hp.irreducible_map_of_natDegree_coprime (Fact.out : Irreducible p) hcop
  let : Fact (Irreducible (p.map (algebraMap k S))) := ⟨hq⟩
  refine ⟨s, hs, S, hfinite, inferInstance, hcop, hsplit, hq, ?_⟩
  dsimp only
  exact hgen S (algebraMap k S) (p.map (algebraMap k S)) dvd_rfl hsplit

end Stacks.Chow
