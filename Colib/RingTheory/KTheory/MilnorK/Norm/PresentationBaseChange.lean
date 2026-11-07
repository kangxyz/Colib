/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport
public import Colib.RingTheory.AdjoinRoot.MapEquiv

/-!
# Comparing actual simple-norm presentations after a mixed restriction

When both literal coefficient images remain irreducible, the actual algebra equivalence
between the two source presentations extends to their coefficient images. If the first
restricted class lies in the existing mixed span, the restricted norm values agree.
The equivalence and its square are constructed inside the proof rather than assumed.

The mixed-span hypothesis is explicit. This supporting theorem alone is not a global
presentation-independence result. It uses no new norm or map definition.

-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

/-- Actual presentation comparisons commute with coefficient extension on a class whose
restriction lies in the native mixed span. Both coefficient images are literal polynomials. -/
theorem simpleMilnorNorm_map_eq_of_mapped_mem_mixedSpan (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (hpφ : Irreducible ((poly p).map φ)) (hqφ : Irreducible ((poly q).map φ))
    (m : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1)) :
    let pφ : MonicIrreducibleOfDegree K ((poly p).map φ).natDegree :=
      ⟨(poly p).map φ, (monic p).map φ, hpφ, rfl⟩
    let j : (k[X] ⧸ Ideal.span {poly p}) →+* (K[X] ⧸ Ideal.span {poly pφ}) :=
      AdjoinRoot.map φ (poly p) (poly pφ) dvd_rfl
    milnorKTransport j (m + 1) x ∈
        milnorKMixedSpan (algebraMap K (K[X] ⧸ Ideal.span {poly pφ})) m →
      milnorKRingMap φ (simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
        milnorKRingMap φ (simpleMilnorNorm q
          (milnorKRingMap f.toRingHom (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) := by
  let pφ : MonicIrreducibleOfDegree K ((poly p).map φ).natDegree :=
    ⟨(poly p).map φ, (monic p).map φ, hpφ, rfl⟩
  let qφ : MonicIrreducibleOfDegree K ((poly q).map φ).natDegree :=
    ⟨(poly q).map φ, (monic q).map φ, hqφ, rfl⟩
  let jp : (k[X] ⧸ Ideal.span {poly p}) →+* (K[X] ⧸ Ideal.span {poly pφ}) :=
    AdjoinRoot.map φ (poly p) (poly pφ) dvd_rfl
  let jq : (k[X] ⧸ Ideal.span {poly q}) →+* (K[X] ⧸ Ideal.span {poly qφ}) :=
    AdjoinRoot.map φ (poly q) (poly qφ) dvd_rfl
  change milnorKTransport jp (m + 1) x ∈
      milnorKMixedSpan (algebraMap K (K[X] ⧸ Ideal.span {poly pφ})) m → _
  intro hx
  obtain ⟨g, hg⟩ := AdjoinRoot.exists_map_algEquiv φ (poly p) (poly q) f
  let fφ : (K[X] ⧸ Ideal.span {poly pφ}) ≃ₐ[K]
      (K[X] ⧸ Ideal.span {poly qφ}) := g
  have hfφ : fφ.toRingHom.comp jp = jq.comp f.toRingHom := hg
  have hmap : milnorKRingMap fφ.toRingHom
      (milnorKRingMap jp (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
        milnorKRingMap jq (milnorKRingMap f.toRingHom
          (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) := by
    calc
      _ = milnorKRingMap (fφ.toRingHom.comp jp)
          (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :=
        milnorKRingMap_comp_apply jp fφ.toRingHom x
      _ = milnorKRingMap (jq.comp f.toRingHom)
          (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :=
        congrArg (fun h : (k[X] ⧸ Ideal.span {poly p}) →+*
          (K[X] ⧸ Ideal.span {poly qφ}) => milnorKRingMap h x) hfφ
      _ = _ := (milnorKRingMap_comp_apply f.toRingHom jq x).symm
  have hnorm : simpleMilnorNorm qφ (milnorKRingMap fφ.toRingHom
      (milnorKRingMap jp (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) =
        simpleMilnorNorm pφ
          (milnorKRingMap jp (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) :=
    simpleMilnorNorm_map_algEquiv_of_mem_mixedSpan pφ qφ fφ
      (milnorKTransport jp (m + 1) x) hx
  calc
    _ = simpleMilnorNorm pφ
        (milnorKRingMap jp (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) :=
      simpleMilnorNorm_map_of_poly_eq_map φ p pφ rfl x
    _ = simpleMilnorNorm qφ (milnorKRingMap fφ.toRingHom
        (milnorKRingMap jp (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) := hnorm.symm
    _ = simpleMilnorNorm qφ (milnorKRingMap jq (milnorKRingMap f.toRingHom
        (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) := congrArg (simpleMilnorNorm qφ) hmap
    _ = _ := (simpleMilnorNorm_map_of_poly_eq_map φ q qφ rfl
      (milnorKRingMap f.toRingHom (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))).symm

end Stacks.Chow

end
