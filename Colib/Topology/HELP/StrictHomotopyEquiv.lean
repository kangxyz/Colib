/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.Cofibration
public import Colib.Topology.MappingCylinder.HomotopyExtension

/-!
# Strict-square homotopy extension and lifting for an actual equivalence

The mapping cylinder and the homotopy extension property construct an
actual lift extending the prescribed boundary, together with a homotopy
relative to that boundary. No relative inverse homotopy is assumed.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/StrictHomotopyEquiv.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, homotopies,
hypotheses and universes are retained; imports use native lower owners. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open TopCat Topology CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
namespace TopCat

/-- Strict-square HELP: an actual homotopy equivalence permits homotopy
lifting across any map with HEP, preserving the given lift on the whole
boundary and keeping the projected homotopy genuinely relative there. -/
theorem homotopyEquiv_strictHELP {A B X Y : TopCat.{u}} {i : A ⟶ B}
    (hi : TopCat.HomotopyExtensionProperty i) (e : ContinuousMap.HomotopyEquiv X Y)
    (a : C(A, X)) (b : C(B, Y)) (w : e.toFun.comp a = b.comp i.hom) :
    ∃ c : C(B, X), c.comp i.hom = a ∧
      Nonempty ((e.toFun.comp c).HomotopyRel b (Set.range i)) := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let M : TopCat.{u} := pushout (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I) f
  let l : X ⊗ TopCat.I ⟶ M := pushout.inl TopCat.ι₁ f
  let t : Y ⟶ M := pushout.inr TopCat.ι₁ f
  let j : X ⟶ M := TopCat.ι₀ ≫ l
  let sq : IsPushout (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I) f l t := IsPushout.of_hasPushout _ _
  let p : M ⟶ Y := TopCat.MappingCylinder.mappingCylinderProjection sq
  have hpj : j ≫ p = f := TopCat.MappingCylinder.mappingCylinderProjection_start sq
  have hpt : t ≫ p = 𝟙 Y := TopCat.MappingCylinder.mappingCylinderProjection_target sq
  have hpl : l ≫ p = fst X TopCat.I ≫ f :=
    TopCat.MappingCylinder.mappingCylinderProjection_cylinder sq
  let S : TopCat.CylinderStrongDeformationRetract j :=
    (TopCat.homotopyExtensionProperty_strongDeformationRetract
      (TopCat.homotopyExtensionProperty_mappingCylinderStart sq)
      (TopCat.MappingCylinder.mappingCylinderStartHomotopyEquiv sq e rfl) rfl).some
  let R : (j.hom.comp S.r.hom).Homotopy (ContinuousMap.id M) :=
    TopCat.homotopyOfCylinder S.H S.H₀ S.H₁
  have hR (s : unitInterval) (x : X) : R (s, j x) = j x :=
    ConcreteCategory.congr_hom S.fixed (x, ULift.up s)
  have hrj (x : X) : S.r (j x) = x := ConcreteCategory.congr_hom S.retract x
  let H : C(unitInterval × A, M) :=
    ⟨fun z => l (a z.2, ULift.up (unitInterval.symm z.1)), by fun_prop⟩
  have hH₀ (x : A) : H (0, x) = (t.hom.comp b) (i x) := by
    change l (a x, ULift.up (unitInterval.symm 0)) = t (b (i x))
    rw [unitInterval.symm_zero]
    have hl := ConcreteCategory.congr_hom sq.w (a x)
    change l (a x, ULift.up 1) = t (e.toFun (a x)) at hl
    exact hl.trans (congrArg t (ContinuousMap.congr_fun w x))
  obtain ⟨Q, hQ₀, hQ⟩ := TopCat.homotopyExtensionProperty_continuous hi M (t.hom.comp b) H hH₀
  let v : C(B, M) := ⟨fun z => Q (1, z), by fun_prop⟩
  have hvi (x : A) : v (i x) = j (a x) := by
    change Q (1, i x) = _
    rw [hQ]
    change l (a x, ULift.up (unitInterval.symm 1)) = l (a x, ULift.up 0)
    rw [unitInterval.symm_one]
  let c : C(B, X) := S.r.hom.comp v
  have hc (x : A) : c (i x) = a x := by
    change S.r (v (i x)) = a x
    rw [hvi, hrj]
  have hcmap : c.comp i.hom = a := by ext x; exact hc x
  let L : (t.hom.comp b).Homotopy v :=
    { toContinuousMap := Q
      map_zero_left := hQ₀
      map_one_left := fun _ => rfl }
  let Rv : (j.hom.comp c).Homotopy v := R.compContinuousMap v
  let K₁ : (e.toFun.comp c).Homotopy (p.hom.comp v) :=
    ((ContinuousMap.Homotopy.refl p.hom).comp Rv).cast
      (by
        ext z
        exact ConcreteCategory.congr_hom hpj (c z)) rfl
  let K₂ : (p.hom.comp v).Homotopy b :=
    ((ContinuousMap.Homotopy.refl p.hom).comp L.symm).cast rfl (by
      ext z
      exact ConcreteCategory.congr_hom hpt (b z))
  have hK₁ (s : unitInterval) (x : A) : K₁ (s, i x) = e.toFun (c (i x)) := by
    change p (R (s, v (i x))) = _
    rw [hvi, hR, hc]
    exact ConcreteCategory.congr_hom hpj (a x)
  have hH (s : unitInterval) (x : A) : p (H (s, x)) = e.toFun (a x) := by
    exact ConcreteCategory.congr_hom hpl (a x, ULift.up (unitInterval.symm s))
  have hK₂ (s : unitInterval) (x : A) : K₂ (s, i x) = (p.hom.comp v) (i x) := by
    change p (Q (unitInterval.symm s, i x)) = p (v (i x))
    rw [hQ, hH, hvi]
    exact (ConcreteCategory.congr_hom hpj (a x)).symm
  let R₁ : (e.toFun.comp c).HomotopyRel (p.hom.comp v) (Set.range i) :=
    { toHomotopy := K₁
      prop' := by rintro s _ ⟨x, rfl⟩; exact hK₁ s x }
  let R₂ : (p.hom.comp v).HomotopyRel b (Set.range i) :=
    { toHomotopy := K₂
      prop' := by rintro s _ ⟨x, rfl⟩; exact hK₂ s x }
  exact ⟨c, hcmap, ⟨R₁.trans R₂⟩⟩

end TopCat
