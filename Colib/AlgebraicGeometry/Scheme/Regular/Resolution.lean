/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.VectorBundle.KernelClosed
public import Colib.CategoryTheory.ExactCategory.Resolution.BoundedComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.FiniteLocallyFreeReplacement

/-!
# Actual finite vector-bundle resolutions on regular schemes

On a quasi-compact regular scheme with the resolution property,
every coherent module sheaf admits a finite tower of actual short exact sequences
whose resolving terms are finite locally free. There is no uniform length bound,
finite-dimensionality assumption, or assertion that vector bundles are globally
projective in the category of sheaves.

The native Stacks results first make a coherent sheaf perfect (Tag 0FDC, degree
zero) and then give an actual bounded finite locally free complex mapping to it
by a quasi-isomorphism (Tag 0F8E). The bounded-complex resolution construction
extracts the finite tower from that map.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [CompactSpace X]
  [AlgebraicGeometry.HasResolutionProperty X]

/-- A coherent sheaf on a regular scheme has an actual finite locally free resolution.
The length may depend on the sheaf. -/
theorem nonempty_finiteResolution_of_regular (hX : AlgebraicGeometry.IsRegular X)
    (M : X.Modules) [M.IsCoherent] :
    Nonempty ((sheafExactStructure X).FiniteResolution
      (fun N : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) M) := by
  letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
  let F := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M
  have hMqc :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1
  have hzero := AlgebraicGeometry.containsZero_isQuasicoherent X
  have hqc : ∀ i : ℤ, (F.X i).IsQuasicoherent := fun i => by
    rcases eq_or_ne i 0 with rfl | hi
    · exact (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm hMqc
    · exact (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
  have hplus : CochainComplex.plus X.Modules F := ⟨0, inferInstance⟩
  have hperf : RingedSpace.IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F) :=
    (AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular hX M).of_iso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app M)
  obtain ⟨E, f, hE, hf⟩ :=
    Stacks.Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_quasiIso
      X F hplus hqc hperf
  letI := hf
  exact E.nonempty_finiteResolution_of_quasiIso_single
    (fun N : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) M f hE.2 hE.1

attribute [stacks 0FDC "Degree-zero coherent perfectness is an input to the finite resolution",
  stacks 0F8E "A bounded finite locally free replacement supplies the actual resolving complex"]
  nonempty_finiteResolution_of_regular

end AlgebraicGeometry.Scheme.Modules
