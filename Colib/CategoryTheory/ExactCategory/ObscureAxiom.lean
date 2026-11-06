/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Composition
public import Colib.CategoryTheory.ExactCategory.Isomorphisms

/-!
# The obscure axiom, with its necessary kernel hypothesis

This proves the deflation cancellation axiom from the exact-category axioms.
The argument is the matrix form of Keller's proof recorded in Bühler,
*Exact Categories*, Proposition 2.15 (dual).
Implementation provenance: adapted from the same-named Quillen source at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The kernel hypothesis is retained:
no weak idempotent completeness or unconditional cancellation is assumed.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- An elementary shear automorphism of a biproduct. -/
def biprodShear {X Y : C} (r : X ⟶ Y) : Y ⊞ X ≅ Y ⊞ X where
  hom := biprod.lift (biprod.fst - biprod.snd ≫ r) biprod.snd
  inv := biprod.lift (biprod.fst + biprod.snd ≫ r) biprod.snd
  hom_inv_id := by
    apply biprod.hom_ext <;> simp [Preadditive.comp_add]
  inv_hom_id := by
    apply biprod.hom_ext <;> simp [Preadditive.comp_sub]

/-- A zero extra column is admissible if an admissible composite factors
through the nonzero column. -/
lemma deflation_desc_zero_of_comp {X Y Z : C} (r : X ⟶ Y) (p : Y ⟶ Z)
    (hrp : E.deflation (r ≫ p)) :
    E.deflation (biprod.desc p (0 : X ⟶ Z)) := by
  have h := E.deflation_comp (biprodShear r).hom (biprod.desc p (r ≫ p))
    (E.deflation_of_iso (biprodShear r)) (E.deflation_biprod_desc p (r ≫ p) hrp)
  convert h using 1
  apply biprod.hom_ext'
  · simp [biprodShear]
  · simp [biprodShear, Preadditive.sub_comp]

/-- Projection exhibits a pushout of a block-diagonal map. -/
lemma isPushout_biprod_map_fst {K Y X : C} (k : K ⟶ Y) :
    IsPushout (biprod.fst : K ⊞ X ⟶ K) (biprod.map k (𝟙 X))
      k (biprod.fst : Y ⊞ X ⟶ Y) := by
  apply IsPushout.mk' (by simp)
  · intro T a b _ h
    simpa using congrArg (fun z => (biprod.inl : Y ⟶ Y ⊞ X) ≫ z) h
  · intro T a b h
    refine ⟨biprod.inl ≫ b, ?_, ?_⟩
    · simpa using congrArg (fun z => (biprod.inl : K ⟶ K ⊞ X) ≫ z) h.symm
    · apply biprod.hom_ext'
      · simp
      · have hz := congrArg (fun z => (biprod.inr : X ⟶ K ⊞ X) ≫ z) h
        simpa using hz

/-- A kernel of `p`, together with the untouched summand, is the kernel of
`[p,0]`. This statement only uses the supplied kernel universal property. -/
def kernelForkBiprodDescZeroIsLimit {K Y Z X : C} {k : K ⟶ Y} {p : Y ⟶ Z}
    (hkp : k ≫ p = 0) (hk : IsLimit (KernelFork.ofι k hkp)) :
    IsLimit (KernelFork.ofι (biprod.map k (𝟙 X))
      (show biprod.map k (𝟙 X) ≫ biprod.desc p (0 : X ⟶ Z) = 0 by
        ext <;> simp [hkp])) := by
  let : Mono k := Fork.IsLimit.mono hk
  refine KernelFork.IsLimit.ofι _ _
    (fun {W} a ha => biprod.lift
      (hk.lift (KernelFork.ofι (a ≫ biprod.fst) (by
        simpa [biprod.desc_eq, Category.assoc] using ha))) (a ≫ biprod.snd)) ?_ ?_
  · intro W a ha
    apply biprod.hom_ext
    · simpa using hk.fac (KernelFork.ofι (a ≫ biprod.fst) (by
        simpa [biprod.desc_eq, Category.assoc] using ha)) WalkingParallelPair.zero
    · simp
  · intro W a ha m hm
    apply biprod.hom_ext
    · apply (cancel_mono k).1
      have h := congrArg (fun z => z ≫ (biprod.fst : Y ⊞ X ⟶ Y)) hm
      simp only [Category.assoc, biprod.map_fst,
        biprod.lift_fst] at h ⊢
      rw [h]
      exact (hk.fac (KernelFork.ofι (a ≫ biprod.fst) (by
        simpa [biprod.desc_eq, Category.assoc] using ha)) WalkingParallelPair.zero).symm
    · simpa using congrArg (fun z => z ≫ (biprod.snd : Y ⊞ X ⟶ X)) hm

/-- The obscure axiom for deflations: cancellation is valid when the surviving
map has a kernel. The kernel is an actual categorical universal property. -/
lemma deflation_of_comp_of_isKernel {X Y Z K : C} (r : X ⟶ Y) (p : Y ⟶ Z)
    {k : K ⟶ Y} (hkp : k ≫ p = 0) (hk : IsLimit (KernelFork.ofι k hkp))
    (hrp : E.deflation (r ≫ p)) : E.deflation p := by
  have hdesc := E.deflation_desc_zero_of_comp r p hrp
  have hcon := E.conflation_of_isKernel _ (kernelForkBiprodDescZeroIsLimit hkp hk (X := X)) hdesc
  have hmap := E.inflation_of_conflation hcon
  have hi : E.inflation k := E.inflation.of_isPushout (isPushout_biprod_map_fst k (X := X)) hmap
  let hc := E.cokernel _ hcon
  apply E.deflation_of_isCokernel hkp _ hi
  refine CokernelCofork.IsColimit.ofπ p hkp
    (fun {W} f hf => hc.desc (CokernelCofork.ofπ (biprod.desc f (0 : X ⟶ W)) (by
      ext <;> simp [hf]))) ?_ ?_
  · intro W f hf
    have h := hc.fac (CokernelCofork.ofπ (biprod.desc f (0 : X ⟶ W)) (by
      ext <;> simp [hf])) WalkingParallelPair.one
    simpa using congrArg (fun z => (biprod.inl : Y ⟶ Y ⊞ X) ≫ z) h
  · intro W f hf m hm
    apply Cofork.IsColimit.hom_ext hc
    change biprod.desc p (0 : X ⟶ Z) ≫ m = _
    calc
      _ = biprod.desc f (0 : X ⟶ W) := by ext <;> simp [hm]
      _ = _ := by
        simpa using (hc.fac (CokernelCofork.ofπ (biprod.desc f (0 : X ⟶ W)) (by
          ext <;> simp [hf])) WalkingParallelPair.one).symm

/-- The usual typeclass formulation of the obscure axiom. -/
lemma deflation_of_comp_of_hasKernel {X Y Z : C} (r : X ⟶ Y) (p : Y ⟶ Z)
    [HasKernel p] (hrp : E.deflation (r ≫ p)) : E.deflation p :=
  E.deflation_of_comp_of_isKernel r p (kernel.condition p) (kernelIsKernel p) hrp

end CategoryTheory.ExactCategory.ExactStructure
