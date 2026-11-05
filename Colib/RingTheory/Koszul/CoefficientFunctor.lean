/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.RingTheory.Koszul.Defs
public import Colib.Util.References
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The exact coefficient functor for native Koszul complexes

The objects are exactly Stacks' `seqComplexTensor`, and a coefficient map acts
by the identity on the exterior factor tensored with that map. Every exterior
term is free, so Mathlib's flat tensor exactness proves that a short exact
sequence of coefficients gives a short exact sequence of these complexes.

This is a lower interface for the motivic Koszul migration. It introduces no
new complex or quotient model, and assumes neither regularity of the sequence
nor flatness or finiteness of the coefficients. The coefficient universe is
independent of the ring universe.
-/

@[expose] public section

open CategoryTheory
open scoped ExteriorAlgebra

universe u v

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The native Koszul complex, functorial in its coefficient module. -/
noncomputable def seqComplexTensorFunctor (f : Fin r → R) :
    ModuleCat.{v} R ⥤ ChainComplex (ModuleCat.{max u v} R) ℕ where
  obj M := seqComplexTensor f M
  map g := {
    f := fun n => ModuleCat.ofHom (g.hom.lTensor (⋀[R]^n (Fin r → R)))
    comm' := fun i j hij => by
      obtain rfl : j + 1 = i := hij
      rw [seqComplexTensor_d, seqComplexTensor_d]
      apply ModuleCat.hom_ext
      exact (LinearMap.rTensor_comp_lTensor _ _ _).trans
        (LinearMap.lTensor_comp_rTensor _ _ _).symm }
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact LinearMap.lTensor_id _ _
  map_comp g h := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact LinearMap.lTensor_comp _ _ _

/-- Coefficient maps act degreewise by the usual left tensor map. -/
@[simp]
theorem seqComplexTensorFunctor_map_f (f : Fin r → R)
    {M N : ModuleCat.{v} R} (g : M ⟶ N) (n : ℕ) :
    ((seqComplexTensorFunctor f).map g).f n =
      ModuleCat.ofHom (g.hom.lTensor (⋀[R]^n (Fin r → R))) := rfl

instance seqComplexTensorFunctor_additive (f : Fin r → R) :
    (seqComplexTensorFunctor.{u,v} f).Additive where
  map_add := by
    intro X Y g h
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact LinearMap.lTensor_add _ _ _

/-- A coefficient short exact sequence remains short exact in every Koszul degree. -/
theorem seqComplexTensorFunctor_degreewise_shortExact (f : Fin r → R)
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) (n : ℕ) :
    ((S.map (seqComplexTensorFunctor f)).map
      (HomologicalComplex.eval _ _ n)).ShortExact where
  exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact Module.Flat.lTensor_exact (⋀[R]^n (Fin r → R))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.lTensor_preserves_injective_linearMap S.f.hom
      hS.moduleCat_injective_f
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.lTensor_surjective (⋀[R]^n (Fin r → R)) hS.moduleCat_surjective_g

/-- The native Koszul coefficient functor sends short exact sequences of modules
into short exact sequences of complexes, without a regularity hypothesis. -/
theorem seqComplexTensorFunctor_shortExact (f : Fin r → R)
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    (S.map (seqComplexTensorFunctor f)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (seqComplexTensorFunctor_degreewise_shortExact f S hS)

end Koszul

attribute [colib_tag "COL-0141"] Koszul.seqComplexTensorFunctor
  Koszul.seqComplexTensorFunctor_map_f Koszul.seqComplexTensorFunctor_degreewise_shortExact
  Koszul.seqComplexTensorFunctor_shortExact

attribute [stacks 0622 "Definition ingredient: exterior-power Koszul terms"]
  Koszul.seqComplexTensorFunctor
attribute [stacks 0623 "Definition ingredient: finite-sequence Koszul complex"]
  Koszul.seqComplexTensorFunctor_shortExact
