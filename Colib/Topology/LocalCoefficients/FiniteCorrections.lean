/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Abelian

/-!
Adapted from `Quillen/Topology/LocalCoefficients/FiniteCorrections.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining its actual coefficient maps.

# Finitely supported monodromy corrections

Component-loop coefficient automorphisms can be composed to prescribe separate
loop actions on finitely many components. The resulting map is an actual natural
isomorphism, and its formula is proved on and off the selected components.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v

namespace FundamentalGroupoid.LocalCoefficients
variable {C : Type u} [Groupoid C] {D : Type v} [Category D]
    {A : C ⥤ D}

/-- A finite product of actual component-supported coefficient automorphisms. -/
def finiteLoopCorrectionIso (hA : AbelianMonodromy A) (l : List (Σ b : C, b ⟶ b)) : A ≅ A :=
  l.foldr (fun g e ↦ componentLoopCorrectionIso hA g.1 g.2 ≪≫ e) (Iso.refl A)

@[simp]
theorem finiteLoopCorrectionIso_nil (hA : AbelianMonodromy A) :
    finiteLoopCorrectionIso hA [] = Iso.refl A := rfl

@[simp]
theorem finiteLoopCorrectionIso_cons (hA : AbelianMonodromy A)
    (g : Σ b : C, b ⟶ b) (l : List (Σ b : C, b ⟶ b)) :
    finiteLoopCorrectionIso hA (g :: l) =
      componentLoopCorrectionIso hA g.1 g.2 ≪≫ finiteLoopCorrectionIso hA l := rfl

/-- Concatenation corresponds to composition in the stated order. -/
theorem finiteLoopCorrectionIso_append (hA : AbelianMonodromy A)
    (l r : List (Σ b : C, b ⟶ b)) :
    finiteLoopCorrectionIso hA (l ++ r) =
      finiteLoopCorrectionIso hA l ≪≫ finiteLoopCorrectionIso hA r := by
  induction l with
  | nil => simp
  | cons g l ih => simp [ih, Iso.trans_assoc]

/-- Components not meeting any of the chosen basepoints are untouched. -/
theorem finiteLoopCorrectionIso_hom_off (hA : AbelianMonodromy A)
    (l : List (Σ b : C, b ⟶ b)) (x : C)
    (h : ∀ g ∈ l, ¬ Nonempty (g.1 ⟶ x)) :
    (finiteLoopCorrectionIso hA l).hom.app x = 𝟙 _ := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    simp only [finiteLoopCorrectionIso_cons, Iso.trans_hom, NatTrans.comp_app]
    rw [componentLoopCorrectionIso_hom_off hA g.2 (h g (by simp)),
      ih (fun z hz ↦ h z (by simp [hz])), Category.id_comp]

/-- On a selected component, all other corrections disappear and the answer
is precisely the prescribed loop transported along any chosen connecting path. -/
theorem finiteLoopCorrectionIso_hom_selected (hA : AbelianMonodromy A)
    (l r : List (Σ b : C, b ⟶ b)) {b x : C} (g : b ⟶ b) (p : b ⟶ x)
    (h : ∀ z ∈ l ++ r, ¬ Nonempty (z.1 ⟶ x)) :
    (finiteLoopCorrectionIso hA (l ++ ⟨b, g⟩ :: r)).hom.app x =
      A.map (inv p ≫ g ≫ p) := by
  rw [finiteLoopCorrectionIso_append]
  simp only [finiteLoopCorrectionIso_cons, Iso.trans_hom, NatTrans.comp_app]
  rw [finiteLoopCorrectionIso_hom_off hA l x (fun z hz ↦ h z (by simp [hz])),
    finiteLoopCorrectionIso_hom_off hA r x (fun z hz ↦ h z (by simp [hz])),
    Category.id_comp, Category.comp_id, componentLoopCorrectionIso_hom_app hA g p]

/-- The groupoid-component condition is exactly the actual topological path relation. -/
theorem nonempty_fundamental_hom_iff_joined {X : Type u} [TopologicalSpace X]
    (x y : X) :
    Nonempty (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ↔ Joined x y := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
    exact ⟨q⟩
  · rintro ⟨p⟩
    exact ⟨Path.Homotopic.Quotient.mk p⟩

/-- A correction supported on one path component is literally identity elsewhere. -/
theorem pathLoopCorrectionIso_hom_off {X : Type u} [TopologicalSpace X]
    {A : System.{u, v} X} (hA : AbelianMonodromy A) {b x : X}
    (g : Path b b) (hx : ¬ Joined b x) :
    (pathLoopCorrectionIso hA g).hom.app (FundamentalGroupoid.mk x) = 𝟙 _ :=
  componentLoopCorrectionIso_hom_off hA (Path.Homotopic.Quotient.mk g)
    (fun h ↦ hx ((nonempty_fundamental_hom_iff_joined b x).mp h))

end FundamentalGroupoid.LocalCoefficients
