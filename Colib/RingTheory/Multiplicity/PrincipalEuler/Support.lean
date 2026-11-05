/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Colib.Util.References
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.Support.FiniteDimensional

/-!
# Finite principal scalar homology from support

Over a commutative Noetherian ring, let `M` and `N` be finite modules and suppose
`Supp N ⊆ Supp M`. If `M / tM` has finite length, both the kernel and the cokernel of
scalar multiplication by `t` on `N` have finite length. In particular, this applies to
every actual subquotient of `M`. No local-ring or scalar-regularity assumption is used.

The scalar maps, kernels and quotients are Mathlib's native objects. The proof uses
`Module.support_quotSMulTop` and the pinned Stacks finite-support criterion, rather than
introducing another prime-filtration model or reproving the finite-length criterion.

## Source provenance

Adapted from `Aglib/RingTheory/Multiplicity/PrincipalEuler/Support.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. That implementation was transferred from
`R5Lab.RingTheory.LocalLength.PrincipalEulerSupport` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, source SHA-256
`5dd0cee73230a6d3cf58f6ac525d8aa880a5bc6e7ad08eb823b6f0e2913099eb`.

This module supplies finite scalar homology. Prime-filtration Euler sums and principal
associativity belong to their separate modules; no motivic comparison is asserted here.
-/

@[expose] public section

namespace Module

universe u v w

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

open scoped Pointwise in
/-- The support of the scalar cokernel is `Supp M ∩ V(t)`. -/
theorem support_quotient_range_lsmul [Module.Finite A M] (t : A) :
    support A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) =
      support A M ∩ PrimeSpectrum.zeroLocus ({t} : Set A) := by
  have hr : LinearMap.range (LinearMap.lsmul A M t) = t • (⊤ : Submodule A M) := by
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists]
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_top, true_and]
  rw [hr]
  exact Module.support_quotSMulTop t

/-- The scalar defining a scalar kernel annihilates that kernel. -/
theorem mem_annihilator_ker_lsmul (t : A) :
    t ∈ Module.annihilator A (LinearMap.ker (LinearMap.lsmul A M t)) := by
  apply Module.mem_annihilator.mpr
  intro x
  apply Subtype.ext
  exact x.property

/-- Without any finiteness assumption, the scalar kernel is supported in `Supp M ∩ V(t)`. -/
theorem support_ker_lsmul_subset (t : A) :
    support A (LinearMap.ker (LinearMap.lsmul A M t)) ⊆
      support A M ∩ PrimeSpectrum.zeroLocus ({t} : Set A) := by
  intro p hp
  refine ⟨Module.support_subset_of_injective (LinearMap.ker (LinearMap.lsmul A M t)).subtype
    (Submodule.subtype_injective _) hp, ?_⟩
  exact Set.singleton_subset_iff.mpr
    ((Module.annihilator_le_of_mem_support hp) (mem_annihilator_ker_lsmul (M := M) t))

private theorem finiteLength_of_support_subset [IsNoetherianRing A]
    [Module.Finite A M] [Module.Finite A N]
    (hM : IsFiniteLength A M) (hs : support A N ⊆ support A M) :
    IsFiniteLength A N := by
  obtain ⟨hfinite, hclosed⟩ :=
    (Module.isFiniteLength_iff_support_finite_subset_closedPoints A M).mp hM
  exact (Module.isFiniteLength_iff_support_finite_subset_closedPoints A N).mpr
    ⟨hfinite.subset hs, hs.trans hclosed⟩

/-- If `M / tM` has finite length, every finite module with support contained in `Supp M`
has finite scalar kernel and scalar cokernel. -/
@[colib_tag "COL-0171",
  colib_ref "aglib_principal_euler_pin" "RingTheory/Multiplicity/PrincipalEuler/Support.lean"
    "adaptation" "Finite scalar homology under support containment and actual subquotients"]
theorem finitePrincipal_of_support_subset [IsNoetherianRing A]
    [Module.Finite A M] [Module.Finite A N] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤)
    (hs : support A N ⊆ support A M) : FinitePrincipal N t := by
  have hlength : IsFiniteLength A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) :=
    Module.length_ne_top_iff.mp hM
  constructor
  · apply Module.length_ne_top_iff.mpr
    apply finiteLength_of_support_subset hlength
    rw [support_quotient_range_lsmul]
    intro p hp
    obtain ⟨hpN, hpt⟩ := support_ker_lsmul_subset (M := N) t hp
    exact ⟨hs hpN, hpt⟩
  · apply Module.length_ne_top_iff.mpr
    apply finiteLength_of_support_subset hlength
    rw [support_quotient_range_lsmul, support_quotient_range_lsmul]
    exact fun _ hp => ⟨hs hp.1, hp.2⟩

/-- Finite scalar cokernel length suffices for finite principal scalar homology on a
finite module over a Noetherian ring. -/
theorem finitePrincipal_of_finite_cokernel [IsNoetherianRing A] [Module.Finite A M]
    (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    FinitePrincipal M t :=
  finitePrincipal_of_support_subset t hM Set.Subset.rfl

/-- Every submodule inherits finite principal scalar homology from finite `M / tM`. -/
theorem finitePrincipal_submodule_of_finite_cokernel [IsNoetherianRing A]
    [Module.Finite A M] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤)
    (U : Submodule A M) : FinitePrincipal U t :=
  finitePrincipal_of_support_subset t hM
    (Module.support_subset_of_injective U.subtype U.subtype_injective)

/-- Every actual subquotient inherits finite principal scalar homology from finite `M / tM`.
No containment hypothesis on `U` and `V` is needed, since `U.submoduleOf V` is the inverse
image of `U` under the inclusion of `V`. -/
@[colib_tag "COL-0171"]
theorem finitePrincipal_subquotient_of_finite_cokernel [IsNoetherianRing A]
    [Module.Finite A M] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤)
    (U V : Submodule A M) : FinitePrincipal (V ⧸ U.submoduleOf V) t :=
  finitePrincipal_of_support_subset t hM
    ((Module.support_subset_of_surjective (U.submoduleOf V).mkQ
      (Submodule.mkQ_surjective _)).trans
      (Module.support_subset_of_injective V.subtype V.subtype_injective))

end Module
