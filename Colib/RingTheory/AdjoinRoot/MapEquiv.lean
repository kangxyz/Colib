/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot

/-!
# Extending an actual root-algebra equivalence along a coefficient map

The given equivalence extends to the two literal coefficient-image root algebras and
commutes with Mathlib's actual AdjoinRoot.map. Both directions are built using the existing
liftAlgHom and identified by their values on the root. No tensor-product model, new carrier,
norm, or adapter is introduced. The coefficient rings need not be fields.

-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

/-- An actual equivalence of root algebras extends along any coefficient homomorphism.
The conclusion includes the literal coefficient-map square, with independent ring universes. -/
theorem exists_map_algEquiv {k S : Type*} [CommRing k] [CommRing S]
    (φ : k →+* S) (p q : k[X]) (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) :
    ∃ eS : AdjoinRoot (p.map φ) ≃ₐ[S] AdjoinRoot (q.map φ),
      eS.toRingHom.comp (AdjoinRoot.map φ p (p.map φ) (dvd_refl _)) =
        (AdjoinRoot.map φ q (q.map φ) (dvd_refl _)).comp e.toRingHom := by
  have hbase (a b : k[X]) (f : AdjoinRoot a →ₐ[k] AdjoinRoot b) :
      ∃ F : AdjoinRoot (a.map φ) →ₐ[S] AdjoinRoot (b.map φ),
        F.toRingHom.comp (AdjoinRoot.map φ a (a.map φ) (dvd_refl _)) =
          (AdjoinRoot.map φ b (b.map φ) (dvd_refl _)).comp f.toRingHom := by
    let j := AdjoinRoot.map φ b (b.map φ) (dvd_refl _)
    let h : AdjoinRoot a →+* AdjoinRoot (b.map φ) := j.comp f.toRingHom
    have hc : h.comp (AdjoinRoot.of a) =
        (AdjoinRoot.of (b.map φ)).comp φ := by
      ext c
      change j (f (AdjoinRoot.of a c)) = AdjoinRoot.of (b.map φ) (φ c)
      have hf : f (AdjoinRoot.of a c) = AdjoinRoot.of b c := by
        simpa only [AdjoinRoot.algebraMap_eq] using f.commutes c
      rw [hf]
      exact AdjoinRoot.map_of φ b (b.map φ) (dvd_refl _) c
    have hz : (a.map φ).eval₂ (algebraMap S (AdjoinRoot (b.map φ)))
        (h (AdjoinRoot.root a)) = 0 := by
      rw [AdjoinRoot.algebraMap_eq, Polynomial.eval₂_map, ← hc,
        ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
    let F : AdjoinRoot (a.map φ) →ₐ[S] AdjoinRoot (b.map φ) :=
      AdjoinRoot.liftAlgHom (a.map φ) (Algebra.ofId S _)
        (h (AdjoinRoot.root a)) hz
    have hFof (c : S) : F (AdjoinRoot.of (a.map φ) c) =
        AdjoinRoot.of (b.map φ) c :=
      AdjoinRoot.liftAlgHom_of (a.map φ) (Algebra.ofId S (AdjoinRoot (b.map φ)))
        (h (AdjoinRoot.root a)) hz c
    have hFroot : F (AdjoinRoot.root (a.map φ)) = h (AdjoinRoot.root a) :=
      AdjoinRoot.liftAlgHom_root (a.map φ) (Algebra.ofId S (AdjoinRoot (b.map φ)))
        (h (AdjoinRoot.root a)) hz
    refine ⟨F, ?_⟩
    apply AdjoinRoot.ringHom_ext
    · ext c
      change F ((AdjoinRoot.map φ a (a.map φ) (dvd_refl _))
        (AdjoinRoot.of a c)) = h (AdjoinRoot.of a c)
      calc
        _ = F (AdjoinRoot.of (a.map φ) (φ c)) :=
          congrArg F (AdjoinRoot.map_of φ a (a.map φ) (dvd_refl _) c)
        _ = AdjoinRoot.of (b.map φ) (φ c) := hFof (φ c)
        _ = h (AdjoinRoot.of a c) := DFunLike.congr_fun hc.symm c
    · change F ((AdjoinRoot.map φ a (a.map φ) (dvd_refl _))
        (AdjoinRoot.root a)) = h (AdjoinRoot.root a)
      exact (congrArg F (AdjoinRoot.map_root φ a (a.map φ) (dvd_refl _))).trans hFroot
  obtain ⟨F, hF⟩ := hbase p q e.toAlgHom
  obtain ⟨G, hG⟩ := hbase q p e.symm.toAlgHom
  let jp := AdjoinRoot.map φ p (p.map φ) (dvd_refl _)
  let jq := AdjoinRoot.map φ q (q.map φ) (dvd_refl _)
  have hFx (x : AdjoinRoot p) : F (jp x) = jq (e x) :=
    DFunLike.congr_fun hF x
  have hGx (x : AdjoinRoot q) : G (jq x) = jp (e.symm x) :=
    DFunLike.congr_fun hG x
  have hFG : F.comp G = AlgHom.id S (AdjoinRoot (q.map φ)) := by
    apply AdjoinRoot.algHom_ext
    change F (G (AdjoinRoot.root (q.map φ))) = AdjoinRoot.root (q.map φ)
    calc
      F (G (AdjoinRoot.root (q.map φ))) =
          F (G (jq (AdjoinRoot.root q))) := by simp only [jq, AdjoinRoot.map_root]
      _ = F (jp (e.symm (AdjoinRoot.root q))) := by rw [hGx]
      _ = jq (e (e.symm (AdjoinRoot.root q))) := hFx _
      _ = AdjoinRoot.root (q.map φ) := by
        simp only [AlgEquiv.apply_symm_apply, jq, AdjoinRoot.map_root]
  have hGF : G.comp F = AlgHom.id S (AdjoinRoot (p.map φ)) := by
    apply AdjoinRoot.algHom_ext
    change G (F (AdjoinRoot.root (p.map φ))) = AdjoinRoot.root (p.map φ)
    calc
      G (F (AdjoinRoot.root (p.map φ))) =
          G (F (jp (AdjoinRoot.root p))) := by simp only [jp, AdjoinRoot.map_root]
      _ = G (jq (e (AdjoinRoot.root p))) := by rw [hFx]
      _ = jp (e.symm (e (AdjoinRoot.root p))) := hGx _
      _ = AdjoinRoot.root (p.map φ) := by
        simp only [AlgEquiv.symm_apply_apply, jp, AdjoinRoot.map_root]
  exact ⟨AlgEquiv.ofAlgHom F G hFG hGF, hF⟩

end AdjoinRoot

end
