/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Comparison
public import Colib.AlgebraicGeometry.Scheme.Regular.Resolution
public import Colib.CategoryTheory.ExactCategory.Resolution.LiftSubcategory

/-!
# Finite vector-bundle resolutions inside the native coherent category

The finite resolution constructed in all module sheaves lifts to the actual
full category of coherent sheaves. Every object and morphism in the tower is
retained. Exactness is measured by the native abelian exact structure.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- Finite local freeness of the underlying sheaf of a native coherent object. -/
def coherentVectorBundle :
    ObjectProperty (SheafOfModules.CoherentModules X.ringCatSheaf) :=
  fun M => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M.obj

instance coherentVectorBundle_isClosedUnderIsomorphisms :
    (coherentVectorBundle X).IsClosedUnderIsomorphisms where
  of_iso e h := by
    exact (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M).prop_of_iso
      ((ObjectProperty.ι (fun M : X.Modules => M.IsCoherent)).mapIso e) h

instance coherentVectorBundle_containsZero : (coherentVectorBundle X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M).prop_of_isZero
      ((ObjectProperty.ι (fun M : X.Modules => M.IsCoherent)).map_isZero (isZero_zero _))⟩

instance coherentVectorBundle_isExtensionClosed :
    (coherentExactStructure X).IsExtensionClosed (coherentVectorBundle X) where
  prop_middle hS h₁ h₃ :=
    ExactStructure.IsExtensionClosed.prop_middle
      (E := sheafExactStructure X) ((coherent_shortExact_iff_map X _).1 hS) h₁ h₃

instance coherentVectorBundle_isKernelClosed :
    (coherentExactStructure X).IsKernelClosed (coherentVectorBundle X) where
  prop_kernel hS h₂ h₃ :=
    ExactStructure.IsKernelClosed.prop_kernel
      (E := sheafExactStructure X) ((coherent_shortExact_iff_map X _).1 hS) h₂ h₃

instance coherentVectorBundle_isClosedUnderFiniteProducts :
    (coherentVectorBundle X).IsClosedUnderFiniteProducts :=
  (coherentExactStructure X).extensionClosed_finiteProducts _

/-- The canonical vector-bundle inclusion detects the actual inherited conflations. -/
theorem vectorBundleToCoherent_conflation_iff [IsLocallyNoetherian X]
    (S : ShortComplex X.Vect) :
    (S.map (vectorBundleToCoherent X)).ShortExact ↔
      (vectorBundleExactStructure X).conflation S :=
  coherent_shortExact_iff_map X _

variable [CompactSpace X] [AlgebraicGeometry.HasResolutionProperty X]

/-- On a regular scheme with the resolution property, every native coherent
object has an actual finite resolution by vector bundles in the coherent category. -/
theorem coherentResolutionHypothesis_of_regular (hX : AlgebraicGeometry.IsRegular X) :
    (coherentExactStructure X).ResolutionHypothesis (coherentVectorBundle X) := by
  letI : IsLocallyNoetherian X := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
  let Q : ObjectProperty X.Modules := fun M => M.IsCoherent
  letI : (sheafExactStructure X).IsExtensionClosed Q :=
    ⟨fun hS h₁ h₃ => CoherentAbelian.isCoherent_X₂_of_shortExact hS h₁ h₃⟩
  letI : (sheafExactStructure X).IsKernelClosed Q :=
    ⟨fun hS h₂ h₃ => CoherentAbelian.isCoherent_X₁_of_shortExact hS h₂ h₃⟩
  letI : Q.IsClosedUnderFiniteProducts :=
    (sheafExactStructure X).extensionClosed_finiteProducts Q
  let F : ExactFunctor (ExactSubcategory.exactStructure (sheafExactStructure X) Q)
      (coherentExactStructure X) :=
    { toFunctor := 𝟭 _
      map_conflation S hS := (coherent_shortExact_iff_map X S).2 hS }
  intro M
  have := M.property
  obtain ⟨T⟩ := nonempty_finiteResolution_of_regular X hX M.obj
  let T' := T.liftToSubcategory
    (fun N hN => by
      have := hN
      exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X N)
    M.property
  exact ⟨F.mapFiniteResolution (fun _ h => h) T'⟩

end AlgebraicGeometry.Scheme.Modules
