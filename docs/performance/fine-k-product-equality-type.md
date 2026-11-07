# Explicit equality type for the fine K-product map

With Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
and Stacks `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`, the following
statement in
[FineProductDecomposition.lean](../../Colib/KTheory/Waldhausen/GilletWaldhausen/FineProductDecomposition.lean)
hit a deterministic `whnf` timeout at 200,000 heartbeats.

```lean
@[simp] theorem boundedTermsAcyclicSingleKEquiv_coe (k : ℕ) :
    (boundedTermsAcyclicSingleKEquiv P k).toMonoidHom =
      boundedTermsAcyclicSingleKMap P k := rfl
```

The native build first reported the deprecated `MonoidHomClass.toMonoidHom`
projection. Replacing that projection alone still produced the timeout.
Scoped `lake env lean --stdin` probes elaborated the file through the affected
declaration on the built imports with `autoImplicit=false`,
`warningAsError=true`, and the Mathlib standard linters. The probes tried
`MonoidHom.ext` and local
`backward.isDefEq.respectTransparency=true`. All three combinations timed out
before a trace at the start of the proof. In the strict `rfl` probe, the
profiler attributed 26.1 s to `CoeT` inference. The diagnostic counters included
77,424 unfoldings of `CochainComplex` and 13,706 of `Structure.cof`.

Giving the equality its existing monoid-homomorphism type let the two terms
elaborate against the same expected type.

```lean
@[simp] theorem boundedTermsAcyclicSingleKEquiv_coe (k : ℕ) :
    @Eq (((ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) →*
        (ofExactCategory (boundedTermsExactStructure P)).K k)
      (MulEquiv.toMonoidHom (boundedTermsAcyclicSingleKEquiv P k))
      (boundedTermsAcyclicSingleKMap P k) := rfl
```

The successful probe used the original heartbeat limit and transparency
settings, with the profiler enabled. It reported 103 ms of elaboration for
the declaration. This compares diagnostic observations with different
instrumentation. The declaration lint subsequently showed that
`MulEquiv.toMonoidHom_eq_coe` simplifies the projection in the probe. The
maintained equality uses `MonoidHom.ofClass`, the simp-normal form of that
projection, and still identifies the same native maps.

Validate the maintained module with
`lake build +Colib.KTheory.Waldhausen.GilletWaldhausen.FineProductDecomposition`
on the pinned basis.
