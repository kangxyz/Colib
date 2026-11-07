/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.IsoFiber.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.Adjunction.Comma

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/FiberedCategory/IsoFiber/Cartesian.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Isomorphism fibers and comma categories via actual cartesian lifts -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.IsoFiber
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) (b : D) (U : StructuredArrow b F)
variable (x : C) (e : b ≅ F.obj x) (f : x ⟶ U.right)
variable (w : e.hom ≫ F.map f = U.hom)
variable [F.IsStronglyCartesian (F.map f) f]

/-- The actual comma arrow supplied by an isomorphism-cartesian lift. -/
def cartesianLiftArrow : (toStructured F b).obj (mk F b x e) ⟶ U :=
  StructuredArrow.homMk f w

/-- A cartesian lift gives the universal arrow from the isomorphism fiber. -/
theorem existsUnique_cartesianFactor (X : IsoFiber F b)
    (a : (toStructured F b).obj X ⟶ U) :
    ∃! h : X ⟶ mk F b x e,
      (toStructured F b).map h ≫ cartesianLiftArrow F b U x e f w = a := by
  let q := inv X.obj.hom ≫ e.hom
  have hw : F.map a.right = q ≫ F.map f := by
    apply (cancel_epi X.obj.hom).1
    change X.obj.hom ≫ F.map a.right = X.obj.hom ≫ (inv X.obj.hom ≫ e.hom) ≫ F.map f
    rw [← Category.assoc X.obj.hom, IsIso.hom_inv_id_assoc, w]
    exact a.w
  let : F.IsHomLift (q ≫ F.map f) a.right := by
    rw [← hw]
    exact IsHomLift.map F a.right
  obtain ⟨k, hk, hu⟩ := Functor.IsStronglyCartesian.universal_property' (p := F)
    (f := F.map f) (φ := f) q a.right
  let := hk.1
  have hkm : F.map k = q := (IsHomLift.eq_of_isHomLift F q k).symm
  let h : X ⟶ mk F b x e := ObjectProperty.homMk (StructuredArrow.homMk k (by
    change X.obj.hom ≫ F.map k = e.hom
    rw [hkm]
    simp [q]))
  refine ⟨h, ?_, ?_⟩
  · apply StructuredArrow.hom_ext
    exact hk.2
  · intro h' hh'
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    apply hu
    refine ⟨?_, ?_⟩
    · have hm : F.map h'.hom.right = q := by
        apply (cancel_epi X.obj.hom).1
        change X.obj.hom ≫ F.map h'.hom.right = X.obj.hom ≫ (inv X.obj.hom ≫ e.hom)
        rw [IsIso.hom_inv_id_assoc]
        exact h'.hom.w
      rw [← hm]
      exact IsHomLift.map F h'.hom.right
    · exact congrArg (fun t => t.right) hh'

/-- The explicit cartesian lift is terminal in the category of universal arrows
from the isomorphism-fiber inclusion to the given comma object. -/
def cartesianLiftIsTerminal :
    IsTerminal (CostructuredArrow.mk (cartesianLiftArrow F b U x e f w)) := by
  let P := fun (A : CostructuredArrow (toStructured F b) U) =>
    existsUnique_cartesianFactor F b U x e f w A.left A.hom
  let k := fun A => (P A).choose
  have hk : ∀ A, (toStructured F b).map (k A) ≫ cartesianLiftArrow F b U x e f w = A.hom :=
    fun A => (P A).choose_spec.1
  refine IsTerminal.ofUniqueHom (fun A => CostructuredArrow.homMk (k A) (hk A)) ?_
  intro A h
  apply CostructuredArrow.hom_ext
  exact (P A).choose_spec.2 h.left (by simpa using h.w)

/-- Isomorphism-cartesian lifts yield a right adjoint to the actual inclusion
of the isomorphism fiber into the structured comma category. -/
theorem toStructured_isLeftAdjoint_of_lifts
    (lifts : ∀ U : StructuredArrow b F,
      ∃ (x : C) (e : b ≅ F.obj x) (f : x ⟶ U.right),
        e.hom ≫ F.map f = U.hom ∧ F.IsStronglyCartesian (F.map f) f) :
    (toStructured F b).IsLeftAdjoint := by
  let : ∀ U : StructuredArrow b F, HasTerminal (CostructuredArrow (toStructured F b) U) := by
    intro U
    obtain ⟨x, e, f, w, hf⟩ := lifts U
    let := hf
    exact (cartesianLiftIsTerminal F b U x e f w).hasTerminal
  exact isLeftAdjoint_of_costructuredArrowTerminals _

end CategoryTheory.IsoFiber
