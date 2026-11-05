/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.TopExtBaseChangeNormalization

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u w z

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

-- The actual complex and augmentation comparisons require no regularity or flatness.
example {n : ℕ} (f : Fin n → R) :
    ((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex (.down ℕ)).obj
      (Koszul.seqComplex f) ≅ Koszul.seqComplex (fun i => algebraMap R A (f i)) :=
  Koszul.seqComplexBaseChangeIso f

-- Empty sequences use the same native top wedge normalization.
example : Koszul.seqExteriorBaseChange (R := R) (A := A) 0 0
    (1 ⊗ₜ[R] Koszul.topGen R 0) = Koszul.topGen A 0 :=
  Koszul.seqExteriorBaseChange_topGen

-- Ext universes remain independent, and the top-class equation includes degree zero.
example [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)]
    [PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A))]
    (f : Fin 0 → R) (hf : Koszul.IsKoszulRegular f)
    (hfA : Koszul.IsKoszulRegular (fun i => algebraMap R A (f i)))
    (N : ModuleCat.{u} R) (m : N) :
    (Ext.mk₀ (Koszul.seqQuotientBaseChangeIso (A := A) f).inv).comp
      ((Koszul.seqTopExtClass f hf N m).mapExactFunctor
        (ModuleCat.extendScalars (algebraMap R A))) (zero_add 0) =
      Koszul.seqTopExtClass (fun i => algebraMap R A (f i)) hfA
        ((ModuleCat.extendScalars (algebraMap R A)).obj N)
        ((1 : A) ⊗ₜ[R, algebraMap R A] m) :=
  Koszul.seqTopExtClass_mapExactFunctor_normalized f hf hfA N m

-- Target regularity is obtained from flatness, rather than supplied as a new assumption.
example [Module.Flat R A] {n : ℕ} (f : Fin n → R) (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular (fun i => algebraMap R A (f i)) :=
  Koszul.isKoszulRegular_algebraMap_of_flat f hf
