/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FiniteCorrections

/-!
Adapted from `Quillen/Topology/LocalCoefficients/FiniteTrackDescent.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining its actual coefficient maps.

# Descent of a finite track discrepancy to an actual coefficient automorphism

Two natural tracks into a groupoid need not induce equal coefficient maps.
For an abelian coefficient system, their discrepancy on finite support extends
to a genuine target coefficient automorphism whenever the target functor
reflects component identifications on that support.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v w

namespace FundamentalGroupoid.LocalCoefficients

/-- Equality of natural transformations propagates along a groupoid arrow. -/
theorem natTrans_app_eq_of_hom {C : Type u} [Groupoid C]
    {D : Type v} [Category D] {F G : C ⥤ D} {α β : F ⟶ G}
    {x y : C} (p : x ⟶ y) (h : α.app x = β.app x) : α.app y = β.app y := by
  apply (cancel_epi (F.map p)).mp
  rw [α.naturality, β.naturality, h]

/-- The finite-support correction is constructed, with its exact action and
its identity value outside the selected components both retained. -/
theorem finite_track_correction_exists {C : Type u} [Groupoid C]
    {D : Type v} [Groupoid D] {E : Type w} [Category E]
    {F G : C ⥤ D} (α β : F ⟶ G) {A : D ⥤ E} (hA : AbelianMonodromy A)
    (s : Finset C)
    (hs : ∀ x ∈ s, ∀ y ∈ s, Nonempty (G.obj x ⟶ G.obj y) → Nonempty (x ⟶ y)) :
    ∃ T : A ≅ A,
      (∀ x ∈ s, A.map (α.app x) ≫ T.hom.app (G.obj x) = A.map (β.app x)) ∧
      (∀ z : D, (∀ x ∈ s, ¬ Nonempty (G.obj x ⟶ z)) → T.hom.app z = 𝟙 _) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Iso.refl A, by simp, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨T, hT, hToff⟩ := ih (fun a ha b hb ↦ hs a (by simp [ha]) b (by simp [hb]))
    by_cases hc : ∃ y ∈ s, Nonempty (G.obj y ⟶ G.obj x)
    · obtain ⟨y, hy, hxy⟩ := hc
      obtain ⟨p⟩ := hs y (by simp [hy]) x (by simp) hxy
      refine ⟨T, ?_, fun z hz ↦ hToff z (fun a ha ↦ hz a (by simp [ha]))⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with hax | ha
      · subst a
        exact natTrans_app_eq_of_hom
          (F := F ⋙ A) (G := G ⋙ A)
          (α := Functor.whiskerRight α A ≫ Functor.whiskerLeft G T.hom)
          (β := Functor.whiskerRight β A) p (hT y hy)
      · exact hT a ha
    · have hdisjoint : ∀ y ∈ s, ¬ Nonempty (G.obj y ⟶ G.obj x) := by
        intro y hy h
        exact hc ⟨y, hy, h⟩
      let U := componentLoopCorrectionIso hA (G.obj x) (inv (α.app x) ≫ β.app x)
      refine ⟨T ≪≫ U, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with hax | ha
        · subst a
          change A.map (α.app x) ≫ (T.hom.app (G.obj x) ≫ U.hom.app (G.obj x)) = _
          rw [hToff (G.obj x) hdisjoint, Category.id_comp]
          exact (map_eq_map_comp_loopCorrection hA (β.app x) (α.app x)).symm
        · have hd : ¬ Nonempty (G.obj x ⟶ G.obj a) := by
            rintro ⟨p⟩
            exact hdisjoint a ha ⟨inv p⟩
          change A.map (α.app a) ≫ (T.hom.app (G.obj a) ≫ U.hom.app (G.obj a)) = _
          change A.map (α.app a) ≫ (T.hom.app (G.obj a) ≫
            (componentLoopCorrectionIso hA (G.obj x)
              (inv (α.app x) ≫ β.app x)).hom.app (G.obj a)) = _
          rw [componentLoopCorrectionIso_hom_off _ _ hd, Category.comp_id, hT a ha]
      · intro z hz
        change T.hom.app z ≫ U.hom.app z = _
        rw [hToff z (fun a ha ↦ hz a (by simp [ha])), Category.id_comp]
        exact componentLoopCorrectionIso_hom_off hA _ (hz x (by simp))

end FundamentalGroupoid.LocalCoefficients
