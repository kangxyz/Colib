/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.AdjoinRoot.MapEquiv

/-! Uncompiled consumers of actual coefficient-extension equivalences of root algebras. -/

noncomputable section

open Polynomial

universe u v

variable {k : Type u} {S : Type v} [CommRing k] [CommRing S]

example (φ : k →+* S) (p q : k[X]) (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) :
    ∃ eS : AdjoinRoot (p.map φ) ≃ₐ[S] AdjoinRoot (q.map φ),
      eS.toRingHom.comp (AdjoinRoot.map φ p (p.map φ) dvd_rfl) =
        (AdjoinRoot.map φ q (q.map φ) dvd_rfl).comp e.toRingHom :=
  AdjoinRoot.exists_map_algEquiv φ p q e

example (φ : k →+* S) (p q : k[X]) (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) :
    ∃ eS : AdjoinRoot (p.map φ) ≃ₐ[S] AdjoinRoot (q.map φ),
      ∀ x : AdjoinRoot p,
        eS (AdjoinRoot.map φ p (p.map φ) dvd_rfl x) =
          AdjoinRoot.map φ q (q.map φ) dvd_rfl (e x) := by
  obtain ⟨eS, heS⟩ := AdjoinRoot.exists_map_algEquiv φ p q e
  exact ⟨eS, fun x => DFunLike.congr_fun heS x⟩

end
