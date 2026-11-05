/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.RelativeCylinder
public import Colib.Topology.MappingCylinder.Diagram

/-!
# Cofibrations for relative mapping-cylinder latching maps

The square-extension theorem makes the relative latching map of a map of
mapping cylinders a cofibration whenever both horizontal transition maps
have HEP. In particular, no relative latching HEP is assumed in the
sequential homotopy-invariance argument.
-/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremA/RealizationPushoutLatching.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, prescribed forward
comparisons, deformation homotopies, hypotheses and universes are retained.
Only namespace/import ownership and unnecessary broad imports change.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u v w

namespace TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The relative latching map for a map of mapping cylinders has HEP when
both the source and target transition maps have HEP. -/
theorem homotopyExtensionProperty_mappingCylinderLatching
    {A B C D M N Q : TopCat.{u}}
    {i : A ⟶ B} {j : C ⟶ D} {f : A ⟶ C} {f' : B ⟶ D}
    {lM : A ⊗ TopCat.I ⟶ M} {cM : C ⟶ M}
    {lN : B ⊗ TopCat.I ⟶ N} {cN : D ⟶ N}
    {bQ : B ⟶ Q} {mQ : M ⟶ Q} {m : M ⟶ N} {q : Q ⟶ N}
    (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f lM cM)
    (sqN : IsPushout (TopCat.ι₁ : B ⟶ B ⊗ TopCat.I) f' lN cN)
    (sqQ : IsPushout i (TopCat.ι₀ ≫ lM) bQ mQ)
    (hi : TopCat.HomotopyExtensionProperty i) (hj : TopCat.HomotopyExtensionProperty j)
    (w : i ≫ f' = f ≫ j)
    (hmline : (i ▷ TopCat.I) ≫ lN = lM ≫ m)
    (hmtarget : j ≫ cN = cM ≫ m)
    (hbq : bQ ≫ q = TopCat.ι₀ ≫ lN) (hmq : mQ ≫ q = m) :
    TopCat.HomotopyExtensionProperty q := by
  intro Z k H hzero
  have hH₀ : ∀ x, H (x, ULift.up 0) = k (q x) :=
    fun x ↦ ConcreteCategory.congr_hom hzero x
  have hqB : ∀ b, q (bQ b) = lN (b, ULift.up 0) :=
    fun b ↦ ConcreteCategory.congr_hom hbq b
  have hqM : ∀ x, q (mQ x) = m x :=
    fun x ↦ ConcreteCategory.congr_hom hmq x
  have hmL : ∀ a s, m (lM (a, ULift.up s)) = lN (i a, ULift.up s) :=
    fun a s ↦ (ConcreteCategory.congr_hom hmline (a, ULift.up s)).symm
  have hmC : ∀ c, m (cM c) = cN (j c) :=
    fun c ↦ (ConcreteCategory.congr_hom hmtarget c).symm
  let HC : C(I × C, Z) := ⟨fun p ↦ H (mQ (cM p.2), ULift.up p.1), by fun_prop⟩
  let kC : C(D, Z) := k.hom.comp cN.hom
  have hHC₀ : ∀ c, HC (0, c) = kC (j c) := by
    intro c
    change H (mQ (cM c), ULift.up 0) = k (cN (j c))
    rw [hH₀, hqM, hmC]
  obtain ⟨V, hV₀, hVj⟩ := TopCat.homotopyExtensionProperty_continuous hj Z kC HC hHC₀
  let kB : C(B × I, Z) := ⟨fun p ↦ k (lN (p.1, ULift.up p.2)), by fun_prop⟩
  let HA : C((A × I) × I, Z) :=
    ⟨fun p ↦ H (mQ (lM (p.1.1, ULift.up p.1.2)), ULift.up p.2), by fun_prop⟩
  let H₀ : C(B × I, Z) := ⟨fun p ↦ H (bQ p.1, ULift.up p.2), by fun_prop⟩
  let H₁ : C(B × I, Z) := ⟨fun p ↦ V (p.2, f' p.1), by fun_prop⟩
  have hkA : ∀ a s, HA ((a, s), 0) = kB (i a, s) := by
    intro a s
    change H (mQ (lM (a, ULift.up s)), ULift.up 0) = k (lN (i a, ULift.up s))
    rw [hH₀, hqM, hmL]
  have hk₀ : ∀ b, H₀ (b, 0) = kB (b, 0) := by
    intro b
    change H (bQ b, ULift.up 0) = k (lN (b, ULift.up 0))
    rw [hH₀, hqB]
  have hk₁ : ∀ b, H₁ (b, 0) = kB (b, 1) := by
    intro b
    change V (0, f' b) = k (lN (b, ULift.up 1))
    rw [hV₀]
    exact congrArg k (ConcreteCategory.congr_hom sqN.w b).symm
  have hA₀ : ∀ a t, HA ((a, 0), t) = H₀ (i a, t) := by
    intro a t
    change H (mQ (lM (a, ULift.up 0)), ULift.up t) = H (bQ (i a), ULift.up t)
    exact congrArg (fun x ↦ H (x, ULift.up t)) (ConcreteCategory.congr_hom sqQ.w a).symm
  have hA₁ : ∀ a t, HA ((a, 1), t) = H₁ (i a, t) := by
    intro a t
    change H (mQ (lM (a, ULift.up 1)), ULift.up t) = V (t, f' (i a))
    have h1 : lM (a, ULift.up 1) = cM (f a) := ConcreteCategory.congr_hom sqM.w a
    have h2 : f' (i a) = j (f a) := ConcreteCategory.congr_hom w a
    rw [h1, h2, hVj]
    rfl
  obtain ⟨K, hK₀, hKA, hKL, hKR⟩ :=
    TopCat.homotopyExtensionProperty_interval_square_extension hi kB HA H₀ H₁ hkA hk₀ hk₁ hA₀ hA₁
  let K' : (B ⊗ TopCat.I) ⊗ TopCat.I ⟶ Z :=
    TopCat.ofHom ⟨fun p : (B × TopCat.I) × TopCat.I ↦
      K ((p.1.1, p.1.2.down), p.2.down), by fun_prop⟩
  let V' : D ⊗ TopCat.I ⟶ Z := TopCat.ofHom ⟨fun p ↦ V (p.2.down, p.1), by fun_prop⟩
  have hKV : (TopCat.ι₁ ▷ TopCat.I) ≫ K' = (f' ▷ TopCat.I) ≫ V' := by
    ext ⟨b, t⟩
    exact hKR b t.down
  let sqNI := sqN.map (tensorRight TopCat.I)
  let W := sqNI.desc K' V' hKV
  have hlW : (lN ▷ TopCat.I) ≫ W = K' := sqNI.inl_desc _ _ _
  have hcW : (cN ▷ TopCat.I) ≫ W = V' := sqNI.inr_desc _ _ _
  have hW₀ : TopCat.ι₀ ≫ W = k := by
    apply sqN.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hlW]
      ext ⟨b, s⟩
      exact hK₀ b s.down
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hcW]
      ext d
      exact hV₀ d
  have sqMI : IsPushout (TopCat.ι₁ ▷ TopCat.I) (f ▷ TopCat.I)
      (lM ▷ TopCat.I) (cM ▷ TopCat.I) := sqM.map (tensorRight TopCat.I)
  have sqQI : IsPushout (i ▷ TopCat.I) ((TopCat.ι₀ ≫ lM) ▷ TopCat.I)
      (bQ ▷ TopCat.I) (mQ ▷ TopCat.I) := sqQ.map (tensorRight TopCat.I)
  have hmW : (m ▷ TopCat.I) ≫ W = (mQ ▷ TopCat.I) ≫ H := by
    apply sqMI.hom_ext
    · rw [← Category.assoc, ← comp_whiskerRight, ← hmline, comp_whiskerRight,
        Category.assoc, hlW]
      ext ⟨⟨a, s⟩, t⟩
      exact hKA a s.down t.down
    · rw [← Category.assoc, ← comp_whiskerRight, ← hmtarget, comp_whiskerRight,
        Category.assoc, hcW]
      ext ⟨c, t⟩
      exact hVj t.down c
  refine ⟨W, hW₀, ?_⟩
  apply sqQI.hom_ext
  · rw [← Category.assoc, ← comp_whiskerRight, hbq, comp_whiskerRight,
      Category.assoc, hlW]
    ext ⟨b, t⟩
    exact hKL b t.down
  · rw [← Category.assoc, ← comp_whiskerRight, hmq, hmW]

/-- The canonical relative latching map in an actual mapping-cylinder
diagram has HEP as soon as both diagram transition maps do. -/
theorem mappingCylinderLatchingMap_hep
    {J : Type v} [Category.{w} J]
    {F G : J ⥤ TopCat.{u}} (η : F ⟶ G) {j k : J} (a : j ⟶ k)
    (hF : TopCat.HomotopyExtensionProperty (F.map a))
    (hG : TopCat.HomotopyExtensionProperty (G.map a)) :
    TopCat.HomotopyExtensionProperty (mappingCylinderLatchingMap η a) := by
  apply homotopyExtensionProperty_mappingCylinderLatching
    (mappingCylinderDiagramSquare η j) (mappingCylinderDiagramSquare η k)
    (IsPushout.of_hasPushout (F.map a) ((mappingCylinderDiagramStart η).app j)) hF hG
  · exact η.naturality a
  · exact (mappingCylinderDiagramLine η).naturality a
  · exact (mappingCylinderDiagramTarget η).naturality a
  · exact mappingCylinderLatchingMap_inl η a
  · exact mappingCylinderLatchingMap_inr η a

end TopCat
