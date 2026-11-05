/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingCylinder.Basic
public import Colib.Topology.Homotopy.IntervalEndpoints

/-!
# Homotopy extension for the mapping-cylinder start
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/MappingCylinder/HomotopyExtension.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, homotopies and
pushout universal properties are retained, with native namespace and import ownership.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat

/-- The initial endpoint of an arbitrary mapping cylinder has HEP. -/
theorem homotopyExtensionProperty_mappingCylinderStart
    {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    TopCat.HomotopyExtensionProperty (TopCat.ι₀ ≫ l) := by
  intro Z k H hH₀
  let J : TopCat.of (A ⊕ A) ⊗ TopCat.I ⟶ Z := TopCat.ofHom
    ⟨fun p ↦ Sum.elim (fun a ↦ H (a, p.2)) (fun a ↦ k (c (f a))) p.1,
      by
        convert (H.hom.continuous.sumElim
          ((k.hom.continuous.comp (c.hom.continuous.comp f.hom.continuous)).comp
            continuous_fst)).comp Homeomorph.sumProdDistrib.continuous using 1
        ext ⟨a, t⟩
        cases a <;> rfl⟩
  have hJ₀ : TopCat.ι₀ ≫ J = TopCat.intervalEndpoints A ≫ l ≫ k := by
    ext a
    cases a with
    | inl a => exact ConcreteCategory.congr_hom hH₀ a
    | inr a => exact congrArg k (ConcreteCategory.congr_hom sq.w a).symm
  obtain ⟨K, hK₀, hK⟩ := TopCat.homotopyExtensionProperty_intervalEndpoints A Z (l ≫ k) J hJ₀
  have hK₁ : (TopCat.ι₁ ▷ TopCat.I) ≫ K = (f ▷ TopCat.I) ≫ fst C TopCat.I ≫ c ≫ k := by
    ext ⟨a, t⟩
    exact ConcreteCategory.congr_hom hK (Sum.inr a, t)
  let sqI := sq.map (tensorRight TopCat.I)
  let L := sqI.desc K (fst C TopCat.I ≫ c ≫ k) hK₁
  have hlL : (l ▷ TopCat.I) ≫ L = K := sqI.inl_desc _ _ _
  have hcL : (c ▷ TopCat.I) ≫ L = fst C TopCat.I ≫ c ≫ k := sqI.inr_desc _ _ _
  refine ⟨L, ?_, ?_⟩
  · apply sq.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hlL, hK₀]
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hcL,
        ← Category.assoc, TopCat.ι₀_fst, Category.id_comp]
  · rw [comp_whiskerRight, Category.assoc, hlL]
    ext ⟨a, t⟩
    exact ConcreteCategory.congr_hom hK (Sum.inl a, t)


end TopCat
