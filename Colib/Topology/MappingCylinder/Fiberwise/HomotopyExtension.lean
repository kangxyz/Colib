/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingCylinder.Basic
public import Colib.Topology.MappingCylinder.Fiberwise.Basic

/-!
# Homotopy extension in a mapping cylinder over a fixed base

The endpoint extension on the cylinder parameter preserves the given map
to the base. Gluing it through the actual mapping-cylinder pushout proves
homotopy extension for the source inclusion with an exact base equation.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/MappingCylinder/Fiberwise/HomotopyExtension.lean` at
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

/-- Mapping-cylinder source homotopy extension with a prescribed common
base map, including the exact base equation on the extended homotopy. -/
theorem mappingCylinderStart_extension_over
    {A C M T Z : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (base : C ⟶ T) (q : Z ⟶ T) (k : M ⟶ Z) (H : A ⊗ TopCat.I ⟶ Z)
    (hH₀ : TopCat.ι₀ ≫ H = (TopCat.ι₀ ≫ l) ≫ k)
    (hk : k ≫ q = TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base)
    (hH : H ≫ q = fst A TopCat.I ≫ f ≫ base) :
    ∃ K : M ⊗ TopCat.I ⟶ Z,
      TopCat.ι₀ ≫ K = k ∧ ((TopCat.ι₀ ≫ l) ▷ TopCat.I) ≫ K = H ∧
        K ≫ q = fst M TopCat.I ≫ TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base := by
  let F : C(A × I, Z) := ⟨fun z ↦ k (l (z.1, ULift.up z.2)), by fun_prop⟩
  let J : C((A ⊕ A) × I, Z) := {
    toFun z := Sum.elim (fun a ↦ H (a, ULift.up z.2)) (fun a ↦ k (c (f a))) z.1
    continuous_toFun := by
      convert ((H.hom.continuous.comp (continuous_fst.prodMk
        (continuous_uliftUp.comp continuous_snd))).sumElim
        ((k.hom.continuous.comp (c.hom.continuous.comp f.hom.continuous)).comp
          continuous_fst)).comp Homeomorph.sumProdDistrib.continuous using 1
      ext ⟨a, t⟩
      cases a <;> rfl }
  have hJ₀ : ∀ a, J (Sum.inl a, 0) = F (a, 0) := fun a ↦ ConcreteCategory.congr_hom hH₀ a
  have hJ₁ : ∀ a, J (Sum.inr a, 0) = F (a, 1) :=
    fun a ↦ congrArg k (ConcreteCategory.congr_hom sq.w a).symm
  let L := intervalEndpointExtension F J hJ₀ hJ₁
  have hpl : ∀ a s, (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) (l (a, ULift.up
    s)) = base (f
    a) := by
    intro a s
    exact ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc sq base) (a, ULift.up s)
  have hpc : ∀ x, (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) (c x) = base x := by
    intro x
    exact ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderProjection_target_assoc sq base) x
  have hFbase : ∀ a s, q (F (a, s)) = base (f a) := by
    intro a s
    exact (ConcreteCategory.congr_hom hk (l (a, ULift.up s))).trans (hpl a s)
  have hJbase : ∀ a t, q (J (a, t)) = base (f (Sum.elim id id a)) := by
    intro a t
    cases a with
    | inl a => exact ConcreteCategory.congr_hom hH (a, ULift.up t)
    | inr a => exact (ConcreteCategory.congr_hom hk (c (f a))).trans (hpc (f a))
  have hLbase : ∀ a s t, q (L ((a, s), t)) = base (f a) :=
    intervalEndpointExtension_invariant F J hJ₀ hJ₁ q (fun a ↦ base (f a)) hFbase hJbase
  let Kc : (A ⊗ TopCat.I) ⊗ TopCat.I ⟶ Z := TopCat.ofHom
    (show C((A × TopCat.I) × TopCat.I, Z) from
      ⟨fun z ↦ L ((z.1.1, z.1.2.down), z.2.down), by fun_prop⟩)
  have hKc₀ : TopCat.ι₀ ≫ Kc = l ≫ k := by
    ext ⟨a, s⟩
    exact intervalEndpointExtension_zero F J hJ₀ hJ₁ a s.down
  have hKcL : (TopCat.ι₀ ▷ TopCat.I) ≫ Kc = H := by
    ext ⟨a, t⟩
    exact intervalEndpointExtension_left F J hJ₀ hJ₁ a t.down
  have hKcR : (TopCat.ι₁ ▷ TopCat.I) ≫ Kc = (f ▷ TopCat.I) ≫ fst C TopCat.I ≫ c ≫ k := by
    ext ⟨a, t⟩
    exact intervalEndpointExtension_right F J hJ₀ hJ₁ a t.down
  let sqI := sq.map (tensorRight TopCat.I)
  let K := sqI.desc Kc (fst C TopCat.I ≫ c ≫ k) hKcR
  have hlK : (l ▷ TopCat.I) ≫ K = Kc := sqI.inl_desc _ _ _
  have hcK : (c ▷ TopCat.I) ≫ K = fst C TopCat.I ≫ c ≫ k := sqI.inr_desc _ _ _
  refine ⟨K, ?_, ?_, ?_⟩
  · apply sq.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hlK, hKc₀]
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hcK,
        ← Category.assoc, TopCat.ι₀_fst, Category.id_comp]
  · rw [comp_whiskerRight, Category.assoc, hlK, hKcL]
  · apply sqI.hom_ext
    · change (l ▷ TopCat.I) ≫ (K ≫ q) = _
      rw [← Category.assoc, hlK]
      ext ⟨⟨a, s⟩, t⟩
      exact (hLbase a s.down t.down).trans (hpl a s.down).symm
    · change (c ▷ TopCat.I) ≫ (K ≫ q) = _
      rw [← Category.assoc, hcK]
      ext ⟨x, t⟩
      exact ConcreteCategory.congr_hom hk (c x)

end TopCat.MappingCylinder
