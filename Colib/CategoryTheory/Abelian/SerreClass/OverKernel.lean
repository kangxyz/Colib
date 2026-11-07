/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
The ordinary categorical geometry uses native Mathlib maps and independent universes. -/

public import Mathlib.CategoryTheory.Abelian.Monomorphisms
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty

/-!
# Ordinary slice kernels and Serre annihilation

The actual kernel functor is base change along zero followed by forgetting the
map to zero. Its cartesian map squares, identity kernel and invertibility test
retain their original hypotheses. Serre-isomorphism objects have kernels in
the original Serre class. No restricted-span category is constructed here.
-/
@[expose] public section




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Abelian.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Epimorphic underlying maps in the slice. -/
abbrev overDeflation (N : C) : MorphismProperty (Over N) :=
  (MorphismProperty.epimorphisms C).inverseImage (Over.forget N)

/-- Monomorphic underlying maps in the slice. -/
abbrev overInflation (N : C) : MorphismProperty (Over N) :=
  (MorphismProperty.monomorphisms C).inverseImage (Over.forget N)

instance overDeflation_baseChange (N : C) : (overDeflation N).IsStableUnderBaseChange where
  of_isPullback sq h := MorphismProperty.of_isPullback
    (P := MorphismProperty.epimorphisms C) (sq.map (Over.forget N)) h

instance overInflation_baseChange (N : C) : (overInflation N).IsStableUnderBaseChange where
  of_isPullback sq h := MorphismProperty.of_isPullback
    (P := MorphismProperty.monomorphisms C) (sq.map (Over.forget N)) h

/-- Kernel as the actual base change along `0 → N`, followed by forgetting the
map to zero. Its objects are canonically kernels, represented by pullbacks. -/
@[implicit_reducible]
def overKernel (N : C) : Over N ⥤ C :=
  Over.pullback (0 : (0 : C) ⟶ N) ⋙ Over.forget (0 : C)

instance overKernel_preservesPullbacks (N : C) :
    PreservesLimitsOfShape WalkingCospan (overKernel N) := by
  dsimp [overKernel]
  infer_instance

/-- The kernel map is the actual pullback of the ambient map along the target
kernel inclusion. Thus epi and mono legs remain epi and mono. -/
theorem overKernel_map_isPullback {N : C} {X Y : Over N} (f : X ⟶ Y) :
    IsPullback ((overKernel N).map f) (pullback.fst X.hom (0 : (0 : C) ⟶ N))
      (pullback.fst Y.hom (0 : (0 : C) ⟶ N)) f.left := by
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback Y.hom (0 : (0 : C) ⟶ N)).flip)
  · dsimp only [overKernel, Functor.comp_map, Over.forget_map, Over.pullback_map_left]
    erw [pullback.lift_snd, Over.w f]
    exact (IsPullback.of_hasPullback X.hom (0 : (0 : C) ⟶ N)).flip
  · dsimp only [overKernel, Functor.comp_map, Over.forget_map, Over.pullback_map_left]
    exact pullback.lift_fst _ _ _

/-- A monomorphism of epimorphisms over the same base is invertible when
its map on kernels is invertible. The proof is an explicit epi-desc argument. -/
theorem over_isIso_of_mono_of_kernel_isIso {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] [IsIso ((overKernel N).map f)] : IsIso f := by
  have : Epi f.left := by
    rw [Preadditive.epi_iff_cancel_zero]
    intro T g hg
    have hkg : pullback.fst Y.hom (0 : (0 : C) ⟶ N) ≫ g = 0 := by
      apply (cancel_epi ((overKernel N).map f)).1
      rw [← Category.assoc, (overKernel_map_isPullback f).w, Category.assoc,
        hg, comp_zero, comp_zero]
    let b := pullback.lift (f := Y.hom) (g := (0 : (0 : C) ⟶ N)) (kernel.ι Y.hom) (0 : kernel Y.hom
      ⟶ (0 : C)) (by simp)
    have hb : b ≫ pullback.fst Y.hom (0 : (0 : C) ⟶ N) = kernel.ι Y.hom :=
      pullback.lift_fst _ _ _
    have hg0 : kernel.ι Y.hom ≫ g = 0 := by rw [← hb, Category.assoc, hkg, comp_zero]
    let d := Abelian.epiDesc Y.hom g hg0
    have hd : Y.hom ≫ d = g := Abelian.comp_epiDesc _ _ _
    have hXd : X.hom ≫ d = 0 := by rw [← Over.w f, Category.assoc, hd, hg]
    have hd0 : d = 0 := (cancel_epi X.hom).1 (by simpa using hXd)
    rw [← hd, hd0, comp_zero]
  have : IsIso f.left := isIso_of_mono_of_epi _
  let : IsIso ((Over.forget N).map f) := inferInstanceAs (IsIso f.left)
  exact isIso_of_reflects_iso f (Over.forget N)

/-- The kernel of the identity is an actual zero object. -/
theorem overKernel_identity_isZero (N : C) : IsZero ((overKernel N).obj (Over.mk (𝟙 N))) := by
  have : IsIso (pullback.snd (𝟙 N) (0 : (0 : C) ⟶ N)) :=
    (IsPullback.of_hasPullback (𝟙 N) (0 : (0 : C) ⟶ N)).isIso_snd_of_isIso
  apply (IsZero.iff_id_eq_zero _).2
  apply (cancel_mono (pullback.snd (𝟙 N) (0 : (0 : C) ⟶ N))).1
  exact (isZero_zero C).eq_of_tgt _ _

/-- The pullback model has its actual kernel inclusion. -/
abbrev overKernelι {N : C} (X : Over N) : (overKernel N).obj X ⟶ X.left :=
  pullback.fst X.hom (0 : (0 : C) ⟶ N)

@[reassoc (attr := simp)]
lemma overKernel_condition {N : C} (X : Over N) : overKernelι X ≫ X.hom = 0 := by
  rw [pullback.condition]
  simp

/-- The base-change model is genuinely a limiting kernel fork. -/
def overKernelIsKernel {N : C} (X : Over N) :
    IsLimit (KernelFork.ofι (overKernelι X) (overKernel_condition X)) :=
  KernelFork.IsLimit.ofι _ _
    (fun g hg => pullback.lift (f := X.hom) (g := (0 : (0 : C) ⟶ N)) g 0 (by simpa using hg))
    (fun g hg => pullback.lift_fst _ _ _)
    (fun g hg m hm => by
      apply pullback.hom_ext
      · simpa using hm
      · exact (isZero_zero C).eq_of_tgt _ _)

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- The kernel of an slice object genuinely belongs to the Serre class. -/
theorem overKernel_mem {N : C} (X : Over N) (hX : P.isoModSerre X.hom) :
    P ((overKernel N).obj X) := by
  exact P.prop_of_iso
    ((overKernelIsKernel X).conePointUniqueUpToIso (kernelIsKernel X.hom)).symm hX.1

end CategoryTheory.Abelian.SerreLocalization
