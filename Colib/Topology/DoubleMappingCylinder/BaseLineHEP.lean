/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.Basic
public import Colib.Topology.Homotopy.RelativeCylinder
public import Colib.Topology.Homotopy.ExtensionContinuous
public import Colib.Topology.Category.TopCat.CompactHausdorffPushout

/-!
# Homotopy extension for the actual double-cylinder base line

If the three specified points of a based span have HEP inclusions, the literal interval running
through their double mapping cylinder has HEP. The two endpoint homotopies first extend on the
actual targets; relative square extension then fills the original source cylinder. This is the
point-set input needed to collapse that contractible interval in the reduced construction.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/BaseLineHEP.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original objects, maps,
point hypotheses, whole stored cylinder paths and universe parameters are
retained. Native namespace and lower-import ownership are used. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat.DoubleCylinder

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (a₀ : A) (b₀ : B) (c₀ : C) (hf : f a₀ = b₀) (hg : g a₀ = c₀)

/-- The literal chosen-point interval inside the original double mapping cylinder. -/
def baseLine : TopCat.I ⟶ D := TopCat.ofHom ⟨fun t ↦ l (a₀, t), by fun_prop⟩

include sq hf hg in
/-- Well-basedness of the original three points makes the whole original base interval
cofibrant; no separation assumption is substituted for homotopy extension. -/
theorem homotopyExtensionProperty_baseLine
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} a₀)))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} b₀)))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} c₀))) :
    TopCat.HomotopyExtensionProperty (baseLine (l := l) a₀) := by
  apply TopCat.homotopyExtensionProperty_of_continuous
  intro Z p H hzero
  have hl (x : A) : l (x, (0 : TopCat.I)) = e (Sum.inl (f x)) :=
    ConcreteCategory.congr_hom sq.w (Sum.inl x)
  have hr (x : A) : l (x, (1 : TopCat.I)) = e (Sum.inr (g x)) :=
    ConcreteCategory.congr_hom sq.w (Sum.inr x)
  let pB : C(B, Z) := ⟨fun b ↦ p (e (Sum.inl b)), by fun_prop⟩
  let pC : C(C, Z) := ⟨fun c ↦ p (e (Sum.inr c)), by fun_prop⟩
  let HB : C(unitInterval × PUnit.{u + 1}, Z) := ⟨fun z ↦ H (z.1, 0), by fun_prop⟩
  let HC : C(unitInterval × PUnit.{u + 1}, Z) := ⟨fun z ↦ H (z.1, 1), by fun_prop⟩
  obtain ⟨KB, hKBzero, hKBpoint⟩ :=
    TopCat.homotopyExtensionProperty_continuous hB Z pB HB (by
      intro a
      change H (0, 0) = p (e (Sum.inl b₀))
      rw [hzero]
      change p (l (a₀, 0)) = _
      rw [hl, hf])
  obtain ⟨KC, hKCzero, hKCpoint⟩ :=
    TopCat.homotopyExtensionProperty_continuous hC Z pC HC (by
      intro a
      change H (0, 1) = p (e (Sum.inr c₀))
      rw [hzero]
      change p (l (a₀, 1)) = _
      rw [hr, hg])
  let pcyl : C(A × unitInterval, Z) := ⟨fun z ↦ p (l (z.1, ULift.up z.2)), by fun_prop⟩
  let side : C((PUnit.{u + 1} × unitInterval) × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, ULift.up z.1.2), by fun_prop⟩
  let cap₀ : C(A × unitInterval, Z) := ⟨fun z ↦ KB (z.2, f z.1), by fun_prop⟩
  let cap₁ : C(A × unitInterval, Z) := ⟨fun z ↦ KC (z.2, g z.1), by fun_prop⟩
  obtain ⟨K, hKzero, hKside, hKleft, hKright⟩ :=
    TopCat.homotopyExtensionProperty_interval_square_extension hA pcyl side cap₀ cap₁
      (fun _ t ↦ hzero (ULift.up t))
      (fun x ↦ (hKBzero (f x)).trans (congrArg p (hl x).symm))
      (fun x ↦ (hKCzero (g x)).trans (congrArg p (hr x).symm))
      (by intro a t; change H (t, 0) = KB (t, f a₀); rw [hf]; exact (hKBpoint t a).symm)
      (by intro a t; change H (t, 1) = KC (t, g a₀); rw [hg]; exact (hKCpoint t a).symm)
  let L : (A ⊗ TopCat.I) ⊗ TopCat.I ⟶ Z :=
    TopCat.ofHom
      ⟨fun z : (A × TopCat.I) × TopCat.I ↦ K ((z.1.1, z.1.2.down), z.2.down), by fun_prop⟩
  let E : TopCat.of (B ⊕ C) ⊗ TopCat.I ⟶ Z := TopCat.ofHom
    ⟨fun z : (B ⊕ C) × TopCat.I ↦
      Sum.elim (fun b ↦ KB (z.2.down, b)) (fun c ↦ KC (z.2.down, c)) z.1,
      by
        convert ((show Continuous (fun z : B × TopCat.I ↦ KB (z.2.down, z.1)) from
          by fun_prop).sumElim
          (show Continuous (fun z : C × TopCat.I ↦ KC (z.2.down, z.1)) from by fun_prop)).comp
            Homeomorph.sumProdDistrib.continuous using 1
        funext z
        rcases z with ⟨b | c, t⟩ <;> rfl⟩
  have w : (TopCat.intervalEndpoints A ▷ TopCat.I) ≫ L = (endMap f g ▷ TopCat.I) ≫ E := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    cases x with
    | inl x => exact hKleft x t.down
    | inr x => exact hKright x t.down
  let sqI := sq.map (tensorRight TopCat.I)
  let R : D ⊗ TopCat.I ⟶ Z := sqI.desc L E w
  have hL (x : A) (s t : TopCat.I) : R (l (x, s), t) = K ((x, s.down), t.down) :=
    ConcreteCategory.congr_hom (sqI.inl_desc L E w) ((x, s), t)
  have hE (x : B ⊕ C) (t : TopCat.I) :
      R (e x, t) = Sum.elim (fun b ↦ KB (t.down, b)) (fun c ↦ KC (t.down, c)) x :=
    ConcreteCategory.congr_hom (sqI.inr_desc L E w) (x, t)
  refine ⟨⟨fun z ↦ R (z.2, ULift.up z.1), by fun_prop⟩, ?_, ?_⟩
  · intro d
    obtain ⟨z, rfl⟩ := TopCat.pushout_sum_surjective sq d
    cases z with
    | inl z => exact (hL z.1 z.2 0).trans (hKzero z.1 z.2.down)
    | inr z =>
      change R (e z, 0) = p (e z)
      rw [hE]
      cases z with
      | inl b => exact hKBzero b
      | inr c => exact hKCzero c
  · intro t s
    exact (hL a₀ s (ULift.up t)).trans (hKside PUnit.unit s.down t)

end TopCat.DoubleCylinder
