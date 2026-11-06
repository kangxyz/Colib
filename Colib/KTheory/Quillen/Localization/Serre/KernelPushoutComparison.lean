/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.CategoryTheory.Abelian.SerreClass.KernelPushoutComparison
public import Colib.KTheory.Quillen.Localization.Serre.KernelPushout
public import Colib.CategoryTheory.QConstruction.Abelian.Cospans
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-!
# Ordinary cospans and comparisons of kernel pushouts

The pushout of an admissible span over a fixed base has a genuine
mono-epi cospan. Its kernel square is bicartesian. A monomorphism of
extensions with the same quotient is itself the pushout of its kernel map.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CategoryTheory.ExactCategory.SerreLocalization

open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Abelian
attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{u} C] [Abelian C]

section SpanPushout
variable {N : C} {X Y : Over N}
    (s : Span (overDeflation N) (overInflation N) X Y)

/-- The ordinary pushout of the underlying span, retaining its map to the base. -/
def overSpanPushoutMap : pushout s.l.left s.r.left ⟶ N :=
  pushout.desc X.hom Y.hom ((Over.w s.l).trans (Over.w s.r).symm)

/-- The pushout of the underlying admissible span, regarded as an object of the slice over `N`
via `overSpanPushoutMap s`. -/
abbrev overSpanPushout : Over N := Over.mk (overSpanPushoutMap s)

/-- The monomorphic leg of the ordinary pushout cospan over the fixed base. -/
def overSpanPushoutInl : X ⟶ overSpanPushout s :=
  Over.homMk (pushout.inl s.l.left s.r.left) (pushout.inl_desc _ _ _)

/-- The epimorphic leg of the ordinary pushout cospan over the fixed base. -/
def overSpanPushoutInr : Y ⟶ overSpanPushout s :=
  Over.homMk (pushout.inr s.l.left s.r.left) (pushout.inr_desc _ _ _)

instance overSpanPushout_hom_epi [Epi X.hom] : Epi (overSpanPushout s).hom :=
  epi_of_epi_fac (Over.w (overSpanPushoutInl s))

instance overSpanPushoutInl_mono : Mono (overSpanPushoutInl s).left := by
  have : Mono s.r.left := s.wr
  exact inferInstanceAs (Mono (pushout.inl s.l.left s.r.left))

instance overSpanPushoutInr_epi : Epi (overSpanPushoutInr s).left := by
  have : Epi s.l.left := s.wl
  exact inferInstanceAs (Epi (pushout.inr s.l.left s.r.left))

/-- The ordinary pushout square is also a pullback in the slice. -/
theorem overSpanPushout_isPullback :
    IsPullback s.l s.r (overSpanPushoutInl s) (overSpanPushoutInr s) := by
  have : Mono s.r.left := s.wr
  apply IsPullback.of_map_of_faithful (Over.forget N)
  change IsPullback s.l.left s.r.left (pushout.inl s.l.left s.r.left)
    (pushout.inr s.l.left s.r.left)
  exact (CommSq.IsPushout.mono_to_isPullback
    (IsPushout.of_hasPushout s.l.left s.r.left).flip).1.flip

/-- Kernel base change carries the actual span to the pullback of its
ordinary cospan on kernels. -/
theorem overSpanPushout_kernel_isPullback :
    IsPullback ((overKernel N).map s.l) ((overKernel N).map s.r)
      ((overKernel N).map (overSpanPushoutInl s))
      ((overKernel N).map (overSpanPushoutInr s)) :=
  (overSpanPushout_isPullback s).map (overKernel N)

instance overSpanPushout_kernelInl_mono :
    Mono ((overKernel N).map (overSpanPushoutInl s)) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms C)
    (overKernel_map_isPullback (overSpanPushoutInl s)).flip inferInstance

instance overSpanPushout_kernelInr_epi :
    Epi ((overKernel N).map (overSpanPushoutInr s)) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
    (overKernel_map_isPullback (overSpanPushoutInr s)).flip inferInstance

/-- The induced square on kernels is an actual pushout square. -/
theorem overSpanPushout_kernel_isPushout :
    IsPushout ((overKernel N).map s.l) ((overKernel N).map s.r)
      ((overKernel N).map (overSpanPushoutInl s))
      ((overKernel N).map (overSpanPushoutInr s)) :=
  (CommSq.IsPullback.epi_to_isPushout (overSpanPushout_kernel_isPullback s).flip).1.flip

/-- The ambient monomorphic cospan leg is the pushout of its kernel map. -/
theorem overSpanPushoutInl_kernel_isPushout [Epi X.hom] :
    IsPushout (overKernelι X) ((overKernel N).map (overSpanPushoutInl s))
      (overSpanPushoutInl s).left (overKernelι (overSpanPushout s)) :=
  overKernel_mono_isPushout (overSpanPushoutInl s)

/-- The underlying ordinary cospan represents the original ambient Q-arrow. -/
theorem overSpanPushout_forget_cospan :
    QConstruction.inflationArrow (overSpanPushoutInl s).left ≫
        QConstruction.surjectionArrow (overSpanPushoutInr s).left =
      (overForgetQ N).map (QConstruction.mkHom _ _ s) :=
  QConstruction.span_cospan_factorization ((overForgetCompatible N).mapSpan s)

/-- The ordinary cospan on kernels represents the original kernel Q-arrow. -/
theorem overSpanPushout_kernel_cospan :
    QConstruction.inflationArrow ((overKernel N).map (overSpanPushoutInl s)) ≫
        QConstruction.surjectionArrow ((overKernel N).map (overSpanPushoutInr s)) =
      (overKernelQ N).map (QConstruction.mkHom _ _ s) := by
  let sq := overSpanPushout_kernel_isPullback s
  rw [← QConstruction.mkHom_cospanSpan]
  change QConstruction.mkHom _ _ _ = QConstruction.mkHom _ _ ((overKernelCompatible N).mapSpan s)
  symm
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · exact sq.isoPullback_hom_fst
  · exact sq.isoPullback_hom_snd

end SpanPushout

end CategoryTheory.ExactCategory.SerreLocalization
