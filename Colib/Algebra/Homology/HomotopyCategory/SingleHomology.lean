/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexFromSingle
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Actual cocycles under the native single-source Hom-complex comparison

The existing Stacks isomorphism from the Hom complex out of a single object to the
termwise additive Hom complex takes an actual cocycle to its actual homology projection.
This fixes the normalization on representatives, not just the existence of an isomorphism.

The proof is adapted from the private `homology_homComplexSingleIso_fromSingleMk` in
`Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The source's separate single-source complex
comparison is replaced by the native Stacks provider. No complex or map is reconstructed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Native single-source evaluation sends an actual cocycle to its homology projection. -/
theorem homology_homComplexSingleIsoCoyonedaComplex_fromSingleMk
    (X : C) (K : CochainComplex C ℤ) (n : ℤ) (f : X ⟶ K.X n)
    (hf : f ≫ K.d n (n + 1) = 0) :
    homologyMap (homComplexSingleIsoCoyonedaComplex X K).hom n
        ((homologyAddEquiv _ _ n).symm
          (.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf))) =
      let H := coyonedaComplex X K
      H.homologyπ n ((H.sc n).abCyclesIso.inv ⟨f, by
        change f ≫ K.d n ((ComplexShape.up ℤ).next n) = 0
        rw [CochainComplex.next ℤ n]
        exact hf⟩) := by
  let L := HomComplex ((singleFunctor C 0).obj X) K
  let H := coyonedaComplex X K
  let E := homComplexSingleIsoCoyonedaComplex X K
  let z := Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf
  let d := leftHomologyData ((singleFunctor C 0).obj X) K n
  have hπ : (homologyAddEquiv _ _ n).symm (.mk z) =
      L.homologyπ n (d.cyclesIso.inv z) :=
    ConcreteCategory.congr_hom d.π_comp_homologyIso_inv z
  have hi : L.iCycles n (d.cyclesIso.inv z) = z.1 :=
    ConcreteCategory.congr_hom d.cyclesIso_inv_comp_iCycles z
  have hc : cyclesMap E.hom n (d.cyclesIso.inv z) =
      (H.sc n).abCyclesIso.inv ⟨f, by
        change f ≫ K.d n ((ComplexShape.up ℤ).next n) = 0
        rw [CochainComplex.next ℤ n]
        exact hf⟩ := by
    apply (AddCommGrpCat.mono_iff_injective (H.iCycles n)).mp inferInstance
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hi]
    erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
    exact Cochain.fromSingleEquiv_fromSingleMk f (zero_add n)
  change homologyMap E.hom n ((homologyAddEquiv _ _ n).symm (.mk z)) = _
  rw [hπ, ← ConcreteCategory.comp_apply, homologyπ_naturality,
    ConcreteCategory.comp_apply, hc]

end CochainComplex.HomComplex
