/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.ObscureAxiom

/-! # Pullback squares between conflations with the same kernel

Implementation provenance: extracted from
`Quillen/Aglib/CategoryTheory/ExactCategory/SpecialFractions.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No filtering machinery is imported.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The short five lemma with identity maps at the endpoints, proved directly
inside the exact category using the obscure axiom. -/
lemma isIso_of_conflations_fixed_ends {A X X' Y : C}
    {i : A ⟶ X} {p : X ⟶ Y} {i' : A ⟶ X'} {p' : X' ⟶ Y}
    {hip : i ≫ p = 0} {hip' : i' ≫ p' = 0}
    (hS : E.conflation (ShortComplex.mk i p hip))
    (hT : E.conflation (ShortComplex.mk i' p' hip'))
    (a : X ⟶ X') (hai : i ≫ a = i') (hap : a ≫ p' = p) : IsIso a := by
  let hk := E.kernel (ShortComplex.mk i p hip) hS
  let hk' := E.kernel (ShortComplex.mk i' p' hip') hT
  let : Mono i := Fork.IsLimit.mono hk
  let : Mono i' := Fork.IsLimit.mono hk'
  have ha : Mono a := by
    apply Preadditive.mono_of_cancel_zero
    intro W f hf
    have hfp : f ≫ p = 0 := by rw [← hap, ← Category.assoc, hf, zero_comp]
    let g := hk.lift (KernelFork.ofι f hfp)
    have hgi : g ≫ i = f := hk.fac _ WalkingParallelPair.zero
    have hgi' : g ≫ i' = 0 := by rw [← hai, ← Category.assoc, hgi, hf]
    have hg : g = 0 := (cancel_mono i').1 (by simpa using hgi')
    rw [← hgi, hg, zero_comp]
  let : Mono a := ha
  let : HasPullback p p' := E.deflation.hasPullback p' (E.deflation_of_conflation hS)
  have hz : (pullback.fst p p' ≫ a - pullback.snd p p') ≫ p' = 0 := by
    simp only [Preadditive.sub_comp, Category.assoc, hap, pullback.condition, sub_self]
  let b : pullback p p' ⟶ A := hk'.lift (KernelFork.ofι (pullback.fst p p' ≫ a - pullback.snd p p')
    hz)
  have hbi : b ≫ i' = pullback.fst p p' ≫ a - pullback.snd p p' := hk'.fac _
    WalkingParallelPair.zero
  let c : pullback p p' ⟶ X := pullback.fst p p' - b ≫ i
  have hca : c ≫ a = pullback.snd p p' := by
    dsimp only [c]
    rw [Preadditive.sub_comp, Category.assoc, hai, hbi, sub_sub_cancel]
  have hc : E.deflation (c ≫ a) := by
    rw [hca]
    exact E.deflation.pullback_snd p p' (E.deflation_of_conflation hS)
  have hda : E.deflation a := E.deflation_of_comp_of_isKernel c a (by simp)
    (kernel.isLimitConeZeroCone a) hc
  exact E.isIso_of_deflation_of_mono a hda

/-- A morphism of conflations which is the identity on kernels gives a
pullback square of the two cokernel maps. -/
lemma isPullback_of_conflations_same_kernel {A X Y B D : C}
    {i : A ⟶ X} {p : X ⟶ Y} {j : A ⟶ B} {r : B ⟶ D}
    {hip : i ≫ p = 0} {hjr : j ≫ r = 0}
    (hS : E.conflation (ShortComplex.mk i p hip))
    (hT : E.conflation (ShortComplex.mk j r hjr))
    (q : X ⟶ B) (f : Y ⟶ D) (hiq : i ≫ q = j) (hpf : p ≫ f = q ≫ r) :
    IsPullback q p r f := by
  let : HasPullback r f := E.deflation.hasPullback f (E.deflation_of_conflation hT)
  let a := pullback.lift q p hpf.symm
  have hpb := E.pullbackConflation_mem hT f
  have hai : i ≫ a = (pullbackConflation Y f (S := ShortComplex.mk j r hjr)).f := by
    apply pullback.hom_ext <;> simp [a, hiq, hip]
  have hap : a ≫ pullback.snd r f = p := by simp [a]
  let : IsIso a := E.isIso_of_conflations_fixed_ends hS hpb a hai hap
  exact IsPullback.of_iso_pullback ⟨hpf.symm⟩ (asIso a) (by simp [a]) (by simp [a])

end CategoryTheory.ExactCategory.ExactStructure
