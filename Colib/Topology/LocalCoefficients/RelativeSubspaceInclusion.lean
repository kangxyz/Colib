/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.RelativeComposition

/-!
Adapted from `Quillen/Topology/LocalCoefficients/RelativeSubspaceInclusion.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.

 # Original relative maps when enlarging the distinguished subspace -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Enlarge the distinguished subspace while keeping the actual ambient coefficient system. -/
def relativeSubspaceInclusion (U V : Set X) (h : U ⊆ V) (A : System.{u, u} X) :
    relativeSingularChainComplex U A ⟶ relativeSingularChainComplex V A :=
  (relativeCoefficientChainIso U (pullbackIdentityIso A)).inv ≫
    relativePushforwardChainMap (ContinuousMap.id X) U V (fun _ hx ↦ h hx) A

/-- The actual map is characterized by its original quotient equation. -/
@[reassoc (attr := simp)]
theorem relativeSubspaceInclusion_quotient (U V : Set X) (h : U ⊆ V)
    (A : System.{u, u} X) :
    cokernel.π (pushforwardChainMap (subspaceInclusion U) A) ≫
        relativeSubspaceInclusion U V h A =
      cokernel.π (pushforwardChainMap (subspaceInclusion V) A) := by
  dsimp only [relativeSubspaceInclusion]
  rw [relativeCoefficientChainIso_inv_quotient_assoc,
    relativePushforwardChainMap_quotient, ← Category.assoc, pushforwardChainMap_id]
  have hi : coefficientChainMap (pullbackIdentityIso A).inv ≫
      coefficientChainMap (pullbackIdentityIso A).hom = 𝟙 (singularChainComplex A) :=
    (coefficientChainIso (pullbackIdentityIso A)).inv_hom_id
  rw [hi, Category.id_comp]

/-- A genuine homotopy equivalence of the actual included subspaces suffices. -/
theorem relativeSubspaceInclusion_quasiIso (U V : Set X) (h : U ⊆ V)
    (A : System.{u, u} X) (e : ContinuousMap.HomotopyEquiv U V)
    (he : e.toFun = subspaceMap (ContinuousMap.id X) U V (fun _ hx ↦ h hx)) :
    QuasiIso (relativeSubspaceInclusion U V h A) := by
  have := relativePushforwardChainMap_quasiIso_of_homotopyEquiv
    (ContinuousMap.id X) U V (fun _ hx ↦ h hx) A
    (ContinuousMap.HomotopyEquiv.refl X) rfl e he
  unfold relativeSubspaceInclusion
  infer_instance

/-- The original spatial relative map commutes with actual subspace enlargement. -/
@[reassoc]
theorem relativeSubspaceInclusion_naturality (f : C(X, Y))
    (U V : Set X) (U' V' : Set Y) (h : U ⊆ V) (h' : U' ⊆ V')
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (A : System.{u, u} Y) :
    relativeSubspaceInclusion U V h (pullback f A) ≫
        relativePushforwardChainMap f V V' hfV A =
      relativePushforwardChainMap f U U' hfU A ≫
        relativeSubspaceInclusion U' V' h' A := by
  apply (cancel_epi
    (cokernel.π (pushforwardChainMap (subspaceInclusion U) (pullback f A)))).mp
  rw [relativeSubspaceInclusion_quotient_assoc, relativePushforwardChainMap_quotient,
    ← Category.assoc, relativePushforwardChainMap_quotient, Category.assoc,
    relativeSubspaceInclusion_quotient]

/-- Enlarging both distinguished subspaces by genuine inclusion homotopy equivalences
detects quasi-isomorphisms of the original spatial relative map. -/
theorem relativePushforwardChainMap_quasiIso_of_subspaceEnlargement (f : C(X, Y))
    (U V : Set X) (U' V' : Set Y) (h : U ⊆ V) (h' : U' ⊆ V')
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (A : System.{u, u} Y)
    (e : ContinuousMap.HomotopyEquiv U V)
    (he : e.toFun = subspaceMap (ContinuousMap.id X) U V (fun _ hx ↦ h hx))
    (e' : ContinuousMap.HomotopyEquiv U' V')
    (he' : e'.toFun = subspaceMap (ContinuousMap.id Y) U' V' (fun _ hx ↦ h' hx))
    (hq : QuasiIso (relativePushforwardChainMap f V V' hfV A)) :
    QuasiIso (relativePushforwardChainMap f U U' hfU A) := by
  have hs := relativeSubspaceInclusion_quasiIso U V h (pullback f A) e he
  have ht := relativeSubspaceInclusion_quasiIso U' V' h' A e' he'
  have hc : QuasiIso (relativePushforwardChainMap f U U' hfU A ≫
      relativeSubspaceInclusion U' V' h' A) := by
    rw [← relativeSubspaceInclusion_naturality f U V U' V' h h' hfU hfV A]
    infer_instance
  exact quasiIso_of_comp_right (relativePushforwardChainMap f U U' hfU A)
    (relativeSubspaceInclusion U' V' h' A)

end FundamentalGroupoid.LocalCoefficients
