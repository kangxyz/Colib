/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingCylinder.Basic
public import Colib.Topology.Homotopy.Extension
public import Colib.Topology.Pushout.Homotopy

/-!
# Collapse of a mapping-cylinder attaching pushout
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/MappingCylinder/PushoutCollapse.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, homotopies and
pushout universal properties are retained, with native namespace and import ownership.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat

/-- The canonical collapse from a mapping-cylinder replacement of an
attaching pushout to the ordinary pushout is an actual homotopy equivalence
whenever the attaching map has HEP. -/
def MappingCylinder.mappingCylinderPushoutCollapseHomotopyEquiv
    {A B C M Q D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    {b : B ⟶ Q} {m : M ⟶ Q} {g : B ⟶ D} {j : C ⟶ D}
    (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (sqQ : IsPushout i (TopCat.ι₀ ≫ l) b m)
    (sqD : IsPushout i f g j) (hi : TopCat.HomotopyExtensionProperty i) :
    ContinuousMap.HomotopyEquiv Q D := by
  let p := TopCat.MappingCylinder.mappingCylinderProjection sqM
  have hq : i ≫ g = (TopCat.ι₀ ≫ l) ≫ p ≫ j := by
    rw [Category.assoc, TopCat.MappingCylinder.mappingCylinderProjection_start_assoc, sqD.w]
  let q := sqQ.desc g (p ≫ j) hq
  have hbq : b ≫ q = g := sqQ.inl_desc _ _ _
  have hmq : m ≫ q = p ≫ j := sqQ.inr_desc _ _ _
  have hstart : TopCat.ι₀ ≫ l ≫ m = i ≫ b := sqQ.w.symm
  let hK := hi Q b (l ≫ m) hstart
  let K := hK.choose
  have hK₀ : TopCat.ι₀ ≫ K = b := hK.choose_spec.1
  have hK : (i ▷ TopCat.I) ≫ K = l ≫ m := hK.choose_spec.2
  have hs : i ≫ TopCat.ι₁ ≫ K = f ≫ c ≫ m := by
    rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hK,
      ← Category.assoc, sqM.w, Category.assoc]
  let s := sqD.desc (TopCat.ι₁ ≫ K) (c ≫ m) hs
  have hgs : g ≫ s = TopCat.ι₁ ≫ K := sqD.inl_desc _ _ _
  have hjs : j ≫ s = c ≫ m := sqD.inr_desc _ _ _
  let HK : TopCat.Homotopy b (g ≫ s) := TopCat.homotopyOfCylinder K hK₀ hgs.symm
  let HR : TopCat.Homotopy (g ≫ 𝟙 D) (g ≫ s ≫ q) :=
    ((TopCat.Homotopy.refl q).comp HK).cast
      (by ext x; exact ConcreteCategory.congr_hom hbq x) rfl
  have hHR : ∀ t a, HR (t, i a) = (𝟙 D) (g (i a)) := by
    intro t a
    change q (K (i a, ULift.up t)) = g (i a)
    have hk := ConcreteCategory.congr_hom hK (a, ULift.up t)
    change K (i a, ULift.up t) = m (l (a, ULift.up t)) at hk
    rw [hk]
    have hm := ConcreteCategory.congr_hom hmq (l (a, ULift.up t))
    change q (m (l (a, ULift.up t))) = j (p (l (a, ULift.up t))) at hm
    rw [hm]
    have hp := ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderProjection_cylinder sqM)
      (a, ULift.up t)
    change p (l (a, ULift.up t)) = f a at hp
    rw [hp]
    exact (ConcreteCategory.congr_hom sqD.w a).symm
  have hjR : j ≫ 𝟙 D = j ≫ s ≫ q := by
    rw [← Category.assoc j s q, hjs, Category.assoc, hmq,
      ← Category.assoc c p j, TopCat.MappingCylinder.mappingCylinderProjection_target,
        Category.id_comp,
      Category.comp_id]
  let right : TopCat.Homotopy (𝟙 D) (s ≫ q) := TopCat.Pushout.pushoutHomotopyOfRelative sqD HR hHR
    hjR
  let sqMI := sqM.map (tensorRight TopCat.I)
  let U : (A ⊗ TopCat.I) ⊗ TopCat.I ⟶ Q := TopCat.ofHom
    ⟨fun z ↦ m (l (z.1.1, ULift.up (TopCat.MappingCylinder.intervalSlide z.2.down z.1.2.down))),
      m.hom.continuous.comp (l.hom.continuous.comp
        (continuous_fst.fst.prodMk (continuous_uliftUp.comp
          (TopCat.MappingCylinder.continuous_intervalSlide.comp ((continuous_uliftDown.comp
            continuous_snd).prodMk
            (continuous_uliftDown.comp continuous_fst.snd))))))⟩
  have hwU : (TopCat.ι₁ ▷ TopCat.I) ≫ U =
      (f ▷ TopCat.I) ≫ fst C TopCat.I ≫ c ≫ m := by
    ext ⟨a, t⟩
    change m (l (a, ULift.up (TopCat.MappingCylinder.intervalSlide t.down 1))) = m (c (f a))
    rw [TopCat.MappingCylinder.intervalSlide_right]
    exact congrArg m (ConcreteCategory.congr_hom sqM.w a)
  let V := sqMI.desc U (fst C TopCat.I ≫ c ≫ m) hwU
  have hlV : (l ▷ TopCat.I) ≫ V = U := sqMI.inl_desc _ _ _
  have hcV : (c ▷ TopCat.I) ≫ V = fst C TopCat.I ≫ c ≫ m := sqMI.inr_desc _ _ _
  have hV₀ : TopCat.ι₀ ≫ V = m := by
    apply sqM.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hlV]
      ext ⟨a, t⟩
      change m (l (a, ULift.up (TopCat.MappingCylinder.intervalSlide 0 t.down))) = m (l (a, t))
      simp only [TopCat.MappingCylinder.intervalSlide_zero]
      rfl
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hcV,
        ← Category.assoc, TopCat.ι₀_fst, Category.id_comp]
  have hV₁ : TopCat.ι₁ ≫ V = m ≫ q ≫ s := by
    apply sqM.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hlV,
        ← Category.assoc m q s, hmq, Category.assoc,
        ← Category.assoc l p, TopCat.MappingCylinder.mappingCylinderProjection_cylinder,
          Category.assoc, hjs]
      ext ⟨a, t⟩
      change m (l (a, ULift.up (TopCat.MappingCylinder.intervalSlide 1 t.down))) = m (c (f a))
      rw [TopCat.MappingCylinder.intervalSlide_one]
      exact congrArg m (ConcreteCategory.congr_hom sqM.w a)
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hcV,
        ← Category.assoc, TopCat.ι₁_fst, Category.id_comp, ← Category.assoc m q s, hmq,
          Category.assoc,
        ← Category.assoc c p, TopCat.MappingCylinder.mappingCylinderProjection_target,
          Category.id_comp, hjs]
  have hUV : (i ▷ TopCat.I) ≫ K = ((TopCat.ι₀ ≫ l) ▷ TopCat.I) ≫ V := by
    rw [hK, comp_whiskerRight, Category.assoc, hlV]
    ext ⟨a, t⟩
    change m (l (a, t)) = m (l (a, ULift.up (TopCat.MappingCylinder.intervalSlide t.down 0)))
    simp only [TopCat.MappingCylinder.intervalSlide_left]
    rfl
  let sqQI := sqQ.map (tensorRight TopCat.I)
  let W := sqQI.desc K V hUV
  have hbW : (b ▷ TopCat.I) ≫ W = K := sqQI.inl_desc _ _ _
  have hmW : (m ▷ TopCat.I) ≫ W = V := sqQI.inr_desc _ _ _
  have hW₀ : TopCat.ι₀ ≫ W = 𝟙 Q := by
    apply sqQ.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hbW, hK₀, Category.comp_id]
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hmW, hV₀, Category.comp_id]
  have hW₁ : TopCat.ι₁ ≫ W = q ≫ s := by
    apply sqQ.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hbW,
        ← Category.assoc b q s, hbq, hgs]
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hmW, hV₁]
  exact ⟨q.hom, s.hom, ⟨(TopCat.homotopyOfCylinder W hW₀ hW₁).symm⟩, ⟨right.symm⟩⟩

@[simp]
theorem MappingCylinder.mappingCylinderPushoutCollapseHomotopyEquiv_toFun
    {A B C M Q D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    {b : B ⟶ Q} {m : M ⟶ Q} {g : B ⟶ D} {j : C ⟶ D}
    (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (sqQ : IsPushout i (TopCat.ι₀ ≫ l) b m)
    (sqD : IsPushout i f g j) (hi : TopCat.HomotopyExtensionProperty i) :
    (TopCat.MappingCylinder.mappingCylinderPushoutCollapseHomotopyEquiv sqM sqQ sqD hi).toFun =
      (sqQ.desc g (TopCat.MappingCylinder.mappingCylinderProjection sqM ≫ j)
        (by rw [Category.assoc, TopCat.MappingCylinder.mappingCylinderProjection_start_assoc,
          sqD.w])).hom := rfl


end TopCat
