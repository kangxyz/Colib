/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionPullbackLinear
public import Colib.CategoryTheory.Monoidal.Action.LinearComposition

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionSpanLinear.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Genuine direct-sum equivariance of the original Q-span extension transport -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
open Functor.LaxLeftLinear
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction

/-- Postcomposing the quotient commutes with direct sum by the identity on middle terms. -/
def extensionPostcomposeAddIso {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (hf : (exactStructure R).deflation f) (S : IsoCategory R)
    (p : (exactStructure R).ExtensionFiber X) :
    S ⊙ₗ ((exactStructure R).extensionFiberPostcompose f hf).obj p ≅
      ((exactStructure R).extensionFiberPostcompose f hf).obj (S ⊙ₗ p) :=
  Core.isoMk ((exactStructure R).extensionProperty Y |>.isoMk
    (Over.isoMk (Iso.refl (S.of ⨿ p.of.obj.left)) (by
      change 𝟙 _ ≫ (coprod.desc 0 p.of.obj.hom ≫ f) =
        coprod.desc 0 (p.of.obj.hom ≫ f)
      simp [coprod.desc_comp])))

/-- The original quotient postcomposition has its identity-on-middle-terms lineator. -/
@[instance_reducible]
def extensionFiberPostcomposeLinear {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (hf : (exactStructure R).deflation f) :
    ((exactStructure R).extensionFiberPostcompose f hf).LaxLeftLinear (IsoCategory R) where
  μₗ S p := (extensionPostcomposeAddIso R f hf S p).hom
  μₗ_naturality_left {S T} h p := by
    apply extensionFiber_hom_ext R
    change coprod.map h.iso.hom (𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ coprod.map h.iso.hom (𝟙 _)
    simp
  μₗ_naturality_right S _ _ g := by
    apply extensionFiber_hom_ext R
    change coprod.map (𝟙 S.of) g.iso.hom.hom.left ≫ 𝟙 _ =
      𝟙 _ ≫ coprod.map (𝟙 S.of) g.iso.hom.hom.left
    simp
  μₗ_associativity S T p := by
    apply extensionFiber_hom_ext R
    change 𝟙 _ ≫ (α_ S.of T.of p.of.obj.left).hom =
      (α_ S.of T.of p.of.obj.left).hom ≫ coprod.map (𝟙 S.of) (𝟙 _) ≫ 𝟙 _
    simp
  μₗ_unitality p := by
    apply extensionFiber_hom_ext R
    change (λ_ p.of.obj.left).hom = 𝟙 _ ≫ (λ_ p.of.obj.left).hom
    simp

/-- The original pullback-then-postcomposition transport retains both genuine lineators. -/
@[instance_reducible]
def extensionSpanTransportLinear {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y) :
    ((exactStructure R).extensionSpanTransport s).LaxLeftLinear (IsoCategory R) := by
  letI := extensionFiberPullbackLinear R s.r
  letI := extensionFiberPostcomposeLinear R s.l s.wl
  exact Functor.LaxLeftLinear.composition
    ((exactStructure R).extensionFiberPullback s.r)
    ((exactStructure R).extensionFiberPostcompose s.l s.wl)

/-- The composite lineator has exactly the canonical pullback comparison on middle terms. -/
theorem extensionSpanTransportLinear_μ_middle {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    letI := extensionSpanTransportLinear R s
    (μₗ ((exactStructure R).extensionSpanTransport s) S p).iso.hom.hom.left =
      extensionPullbackAddHom R s.r S p := by
  change 𝟙 _ ≫ extensionPullbackAddHom R s.r S p = extensionPullbackAddHom R s.r S p
  exact Category.id_comp _

end ModuleCat.FiniteProjective
