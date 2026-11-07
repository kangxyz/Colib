/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Extension

/-! # Homotopy extension from ordinary interval coordinates

Implementation provenance: `Quillen/Topology/HELP/Basic.lean`,
`homotopyExtensionProperty_of_continuous`, at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The categorical cylinder and the
ordinary interval are the existing native objects.
-/
@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat

/-- Ordinary interval extension implies the categorical homotopy extension property. -/
theorem homotopyExtensionProperty_of_continuous {A B : TopCat.{u}} (i : A ⟶ B)
    (hext : ∀ (Z : TopCat.{u}) (f : C(B, Z)) (H : C(unitInterval × A, Z)),
      (∀ a, H (0, a) = f (i a)) →
      ∃ K : C(unitInterval × B, Z), (∀ b, K (0, b) = f b) ∧
        ∀ t a, K (t, i a) = H (t, a)) : TopCat.HomotopyExtensionProperty i := by
  intro Z f H hzero
  let H' : C(unitInterval × A, Z) :=
    ⟨fun p ↦ H (p.2, ULift.up p.1), H.hom.continuous.comp
      (continuous_snd.prodMk (continuous_uliftUp.comp continuous_fst))⟩
  have hzero' : ∀ a, H' (0, a) = f.hom (i a) := fun a ↦
    ConcreteCategory.congr_hom hzero a
  obtain ⟨K, hK₀, hK⟩ := hext Z f.hom H' hzero'
  let K' : B ⊗ TopCat.I ⟶ Z := TopCat.ofHom
    ⟨fun p ↦ K (p.2.down, p.1), K.continuous.comp
      ((continuous_uliftDown.comp continuous_snd).prodMk continuous_fst)⟩
  refine ⟨K', ?_, ?_⟩
  · ext b
    exact hK₀ b
  · ext ⟨a, t⟩
    exact hK t.down a

end TopCat
