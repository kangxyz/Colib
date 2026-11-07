# Existential elimination in finite mixed generation

The Lean 4.35.0 upgrade exposed a deterministic `whnf` timeout at 200,000
heartbeats in `Stacks.Chow.exists_finite_coprime_milnorK_mixed_expansion`.
The source is
[FiniteMixedGeneration.lean](../../Colib/KTheory/MilnorK/FiniteMixedGeneration.lean).
The production diagnosis used Linux x86-64, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and Stacks
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.

The original proof began with two nested patterns.

```lean
  obtain ⟨s, hs, hgen⟩ := exists_finite_milnorK_reduced_mixed_expansion.{u, u} p hp m x
  let : Fact p.natDegree.Prime := ⟨hprime⟩
  obtain ⟨S, hfinite, hcop, hsplit⟩ :=
    exists_coprime_splitting_field_of_finset p.natDegree s
      (fun r hr => (hs r hr).1) (fun r hr => (hs r hr).2)
```

A scoped `lake env lean --stdin -DautoImplicit=false -DwarningAsError=true`
probe used the same source and built imports. The probe enabled `profiler` and
`diagnostics` and inserted trace markers between proof steps. The first
extraction completed and the second ran out of heartbeats. The profiler
attributed 6.1 s and 5.92 s to the two `obtain` calls, with 12.4 s in elaboration.

The repair applies each witness's `Exists.elim` to the existing goal, introduces
the witness and conjunction, and reads the conjuncts with projections.

```lean
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
```

The second probe kept the same compiler, dependency artifacts and heartbeat
budget. It used the profiler without the diagnostic counters or trace markers.
The command succeeded with 1.14 s of elaboration for the theorem. These are
scoped diagnostic observations with different instrumentation. Both proofs use
the same witness theorems, and the result still refers to the actual
intermediate field, coefficient image and root-field map.

Validate the maintained module with
`lake build +Colib.KTheory.MilnorK.FiniteMixedGeneration` on the pinned basis.
