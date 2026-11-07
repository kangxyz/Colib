/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.Cofibration
public import Colib.Topology.MappingCylinder.Fiberwise.Retraction

/-!
# Relative mapping-cylinder deformation over the base

The parameter-preserving cylinder extension also applies to compact-open
path-valued maps. It contracts the source restriction's backtracking loop
without changing the base projection, producing a genuine source strong
deformation retraction over the base.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/MappingCylinder/Fiberwise/RelativeHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat.MappingCylinder

/-- A mapping-cylinder inverse homotopy over the base can be made fixed
on the source inclusion while keeping its entire base projection unchanged. -/
theorem mappingCylinder_relative_retraction_over
    {A C M T : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (base : C ⟶ T) (r : M ⟶ A)
    (hir : (TopCat.ι₀ ≫ l) ≫ r = 𝟙 A)
    (hr : r ≫ f ≫ base = TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base)
    (F : TopCat.Homotopy (r ≫ (TopCat.ι₀ ≫ l)) (𝟙 M))
    (hF : ∀ t m, (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) (F (t, m)) =
      (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) m) :
    ∃ K : TopCat.Homotopy (r ≫ (TopCat.ι₀ ≫ l)) (𝟙 M),
      (∀ t a, K (t, (TopCat.ι₀ ≫ l) a) = (TopCat.ι₀ ≫ l) a) ∧
        ∀ t m, (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) (K (t, m)) =
          (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) m := by
  let j := TopCat.ι₀ ≫ l
  let b := TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base
  have hjbase : ∀ a, b (j a) = base (f a) :=
    fun a ↦ ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderProjection_start_assoc sq base) a
  have hjrbase : ∀ m, b (j (r m)) = b m := by
    intro m
    exact (hjbase (r m)).trans (ConcreteCategory.congr_hom hr m)
  let K := TopCat.retractionBacktrackHomotopy hir F
  have hKbase : ∀ t m, b (K (t, m)) = b m := by
    intro t m
    simp only [K, TopCat.retractionBacktrackHomotopy, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact (hF _ (j (r m))).trans (hjrbase m)
    · exact hF _ m
  let Kc : C(M, C(I, M)) := (K.toContinuousMap.comp ContinuousMap.prodSwap).curry
  let G : C((I × A) × I, M) :=
    ⟨fun z ↦ F (TopCat.shrinkBacktrackTime z.1.1 z.2, j z.1.2), by fun_prop⟩
  have hG₀ : ∀ a, G.curry (0, a) = Kc (j a) := by
    intro a
    ext t
    change F (TopCat.shrinkBacktrackTime 0 t, j a) = K (t, j a)
    rw [TopCat.shrinkBacktrackTime_zero]
    exact (TopCat.retractionBacktrackHomotopy_restrict hir F t a).symm
  let qPath : TopCat.of C(I, M) ⟶ TopCat.of C(I, T) := TopCat.ofHom {
    toFun γ := b.hom.comp γ
    continuous_toFun := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact b.hom.continuous.comp continuous_eval }
  let basePath : C ⟶ TopCat.of C(I, T) := TopCat.ofHom
    ⟨fun x ↦ ContinuousMap.const I (base x), by fun_prop⟩
  let HG : A ⊗ TopCat.I ⟶ TopCat.of C(I, M) := TopCat.ofHom
    ⟨fun z ↦ G.curry (z.2.down, z.1), by fun_prop⟩
  have hHG₀ : TopCat.ι₀ ≫ HG = j ≫ TopCat.ofHom Kc := by
    ext a t
    exact ContinuousMap.congr_fun (hG₀ a) t
  have hKcbase : TopCat.ofHom Kc ≫ qPath = TopCat.MappingCylinder.mappingCylinderProjection sq ≫
    basePath := by
    ext m t
    exact hKbase t m
  have hHGbase : HG ≫ qPath = fst A TopCat.I ≫ f ≫ basePath := by
    ext ⟨a, s⟩ t
    exact (hF _ (j a)).trans (hjbase a)
  obtain ⟨Qcat, hQcat₀, hQcatj, hQcatbase⟩ := mappingCylinderStart_extension_over sq basePath
    qPath (TopCat.ofHom Kc) HG hHG₀ hKcbase hHGbase
  let Q : C(I × M, C(I, M)) := ⟨fun z ↦ Qcat (z.2, ULift.up z.1), by fun_prop⟩
  have hQ₀ : ∀ m, Q (0, m) = Kc m := fun m ↦ ConcreteCategory.congr_hom hQcat₀ m
  have hQj : ∀ t a, Q (t, j a) = G.curry (t, a) := by
    intro t a
    exact ConcreteCategory.congr_hom hQcatj (a, ULift.up t)
  have hQbase : ∀ s m t, b (Q (s, m) t) = b m := by
    intro s m t
    exact ContinuousMap.congr_fun (ConcreteCategory.congr_hom hQcatbase (m, ULift.up s)) t
  let e₀ : C(M, M) := ⟨fun m ↦ Q (1, m) 0, by fun_prop⟩
  let e₁ : C(M, M) := ⟨fun m ↦ Q (1, m) 1, by fun_prop⟩
  let L₀ : (r ≫ j).hom.Homotopy e₀ := {
    toFun z := Q z 0
    continuous_toFun := by fun_prop
    map_zero_left := fun m ↦ by rw [hQ₀]; exact K.map_zero_left m
    map_one_left := fun _ ↦ rfl }
  let L₁ : e₀.Homotopy e₁ := {
    toFun z := Q (1, z.2) z.1
    continuous_toFun := by fun_prop
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun _ ↦ rfl }
  let L₂ : e₁.Homotopy (ContinuousMap.id M) := {
    toFun z := Q (σ z.1, z.2) 1
    continuous_toFun := by fun_prop
    map_zero_left := fun _ ↦ by simp [e₁]
    map_one_left := fun m ↦ by rw [symm_one, hQ₀]; exact K.map_one_left m }
  have hL₀ : ∀ t a, L₀ (t, j a) = j a := by
    intro t a
    change Q (t, j a) 0 = j a
    rw [hQj]
    change F (TopCat.shrinkBacktrackTime t 0, j a) = j a
    simp
  have hL₁ : ∀ t a, L₁ (t, j a) = j a := by
    intro t a
    change Q (1, j a) t = j a
    rw [hQj]
    change F (TopCat.shrinkBacktrackTime 1 t, j a) = j a
    simp
  have hL₂ : ∀ t a, L₂ (t, j a) = j a := by
    intro t a
    change Q (σ t, j a) 1 = j a
    rw [hQj]
    change F (TopCat.shrinkBacktrackTime (σ t) 1, j a) = j a
    simp
  refine ⟨(L₀.trans L₁).trans L₂, ?_, ?_⟩
  · intro t a
    simp only [ContinuousMap.Homotopy.trans_apply]
    split_ifs <;> first | exact hL₀ _ a | exact hL₁ _ a | exact hL₂ _ a
  · intro t m
    simp only [ContinuousMap.Homotopy.trans_apply]
    split_ifs <;> exact hQbase _ m _

/-- The mapping-cylinder source of a specified fiberwise homotopy
equivalence is a genuine strong deformation retract over the base. -/
theorem mappingCylinder_sourceStrongDeformationRetract_over
    {A C M T : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (base : C ⟶ T) (g : C ⟶ A)
    (H : TopCat.Homotopy (f ≫ g) (𝟙 A)) (K : TopCat.Homotopy (g ≫ f) (𝟙 C))
    (hg : g ≫ f ≫ base = base)
    (hH : ∀ t a, base (f (H (t, a))) = base (f a))
    (hK : ∀ t x, base (K (t, x)) = base x) :
    ∃ R : TopCat.CylinderStrongDeformationRetract (TopCat.ι₀ ≫ l),
      R.r ≫ f ≫ base = TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base ∧
        R.H ≫ TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base =
          fst M TopCat.I ≫ TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base := by
  obtain ⟨r, hir, hr, F, hF⟩ := mappingCylinder_exists_source_retraction_over sq base g H K hg hH hK
  obtain ⟨L, hL, hLb⟩ := mappingCylinder_relative_retraction_over sq base r hir hr F hF
  let R : TopCat.CylinderStrongDeformationRetract (TopCat.ι₀ ≫ l) := {
    r := r
    retract := hir
    H := L.h
    H₀ := L.ι₀_h
    H₁ := L.ι₁_h
    fixed := by ext ⟨a, t⟩; exact hL t.down a }
  refine ⟨R, hr, ?_⟩
  ext ⟨m, t⟩
  exact hLb t.down m

end TopCat.MappingCylinder
