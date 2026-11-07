/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Abelian.Devissage.Layers
public import Colib.CategoryTheory.QConstruction.Abelian.Cancellation

/-!
# Recovering layers from abelian Q-spans

An admissible span presents its source as the quotient of its apex subobject
by the image of the kernel of its epimorphic leg. The canonical quotient
isomorphism is proved with its projection equation.
-/
/-!
Implementation provenance: adapted from
`Quillen/Devissage/SpanLayers.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native Mathlib full subcategories, Colib exact structures,
restricted spans, actual realization maps and their universes are retained.
No extension-closure, uniform filtration bound, alternate K-model or Aglib import is added.
-/

@[expose] public section

noncomputable section
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace CategoryTheory.Abelian.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  {X M : C}

/-- The lower subobject attached to an admissible span. -/
def spanLower (s : QConstruction.AbelianSpan X M) : Subobject M :=
  Subobject.mk (kernel.ι s.l ≫ s.r)

/-- The upper subobject attached to an admissible span. -/
def spanUpper (s : QConstruction.AbelianSpan X M) : Subobject M :=
  Subobject.mk s.r

/-- The span's kernel subobject is contained in its apex subobject. -/
lemma spanLower_le_upper (s : QConstruction.AbelianSpan X M) : spanLower s ≤ spanUpper s :=
  Subobject.mk_le_mk_of_comm (kernel.ι s.l) rfl

/-- The chosen subobject representatives do not change the quotient object. -/
def spanQuotientIsoKernel (s : QConstruction.AbelianSpan X M) :
    cokernel (Subobject.ofLE (spanLower s) (spanUpper s) (spanLower_le_upper s)) ≅
      cokernel (kernel.ι s.l) :=
  cokernel.mapIso _ _ (Subobject.underlyingIso (kernel.ι s.l ≫ s.r))
    (Subobject.underlyingIso s.r) (by
      apply (cancel_mono s.r).1
      simp [spanLower, spanUpper, assoc, Subobject.ofLE_arrow])

/-- An epimorphism is the quotient by its kernel. -/
def spanKernelQuotientIso (s : QConstruction.AbelianSpan X M) : cokernel (kernel.ι s.l) ≅ X :=
  (cokernelIsCokernel (kernel.ι s.l)).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι s.l) (kernel.condition s.l))
      (kernelIsKernel s.l))

@[reassoc (attr := simp)]
lemma cokernel_π_spanKernelQuotientIso_hom (s : QConstruction.AbelianSpan X M) :
    cokernel.π (kernel.ι s.l) ≫ (spanKernelQuotientIso s).hom = s.l := by
  exact (cokernelIsCokernel (kernel.ι s.l)).comp_coconePointUniqueUpToIso_hom
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι s.l) (kernel.condition s.l))
      (kernelIsKernel s.l)) WalkingParallelPair.one

/-- The quotient of the layer recovered from a Q-span is its source. -/
def spanQuotientIso (s : QConstruction.AbelianSpan X M) :
    cokernel (Subobject.ofLE (spanLower s) (spanUpper s) (spanLower_le_upper s)) ≅ X :=
  (spanQuotientIsoKernel s).trans (spanKernelQuotientIso s)

/-- The source identification preserves the actual epimorphic leg. -/
@[reassoc (attr := simp)]
lemma cokernel_π_spanQuotientIso_hom (s : QConstruction.AbelianSpan X M) :
    cokernel.π (Subobject.ofLE (spanLower s) (spanUpper s) (spanLower_le_upper s)) ≫
      (spanQuotientIso s).hom = (Subobject.underlyingIso s.r).hom ≫ s.l := by
  simp [spanQuotientIso, spanQuotientIsoKernel, cokernel.mapIso_hom]

variable (P : ObjectProperty C) [P.IsClosedUnderSubobjects]

/-- Recover the actual layer from a Q-span whose source satisfies `P`. -/
def spanLayer (s : QConstruction.AbelianSpan X M) (hX : P X) : Layer P M where
  lower := spanLower s
  upper := spanUpper s
  le := spanLower_le_upper s
  property := P.prop_of_iso (spanQuotientIso s).symm hX

/-- The recovered layer has the original span source as its quotient. -/
def spanLayerQuotientIso (s : QConstruction.AbelianSpan X M) (hX : P X) :
    (spanLayer P s hX).quotient ≅ X := spanQuotientIso s

@[reassoc (attr := simp)]
lemma cokernel_π_spanLayerQuotientIso_hom (s : QConstruction.AbelianSpan X M) (hX : P X) :
    cokernel.π (Subobject.ofLE (spanLayer P s hX).lower (spanLayer P s hX).upper
      (spanLayer P s hX).le) ≫ (spanLayerQuotientIso P s hX).hom =
        (Subobject.underlyingIso s.r).hom ≫ s.l :=
  cokernel_π_spanQuotientIso_hom s

end CategoryTheory.Abelian.Devissage
