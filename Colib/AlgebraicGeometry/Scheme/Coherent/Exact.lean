/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic

/-!
# The exact category of native coherent module sheaves

The native category `AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf`
is abelian on every scheme. Its standard exact structure agrees with short exactness after
its literal full inclusion into module sheaves. No noetherian assumption is needed here;
that assumption enters the comparison from vector bundles.

Implementation provenance: coherent exactness used by
`Quillen/AlgebraicGeometry/Scheme/Coherent/Basic.lean` at `c561118b`, with its Aglib
implementation at `2c34f185fa859e862661f939cd216b07bcccfb26`. We use the existing
native coherent category and its proved abelian structure rather than reconstructing the
affine-local finite-type category of the earlier implementation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- The standard exact structure on the native category of coherent module sheaves. -/
def coherentExactStructure :
    ExactStructure (SheafOfModules.CoherentModules X.ringCatSheaf) :=
  abelianExactStructure _

/-- Short exactness of coherent sheaves is detected by the native full inclusion. -/
theorem coherent_shortExact_iff_map
    (S : ShortComplex (SheafOfModules.CoherentModules X.ringCatSheaf)) :
    S.ShortExact ↔
      (S.map (ObjectProperty.ι (fun M : X.Modules => M.IsCoherent))).ShortExact := by
  have : PreservesFiniteLimits (ObjectProperty.ι (fun M : X.Modules => M.IsCoherent)) :=
    CoherentAbelian.coherentModules_inclusion_preservesFiniteLimits X.ringCatSheaf
  have : PreservesFiniteColimits (ObjectProperty.ι (fun M : X.Modules => M.IsCoherent)) :=
    CoherentAbelian.coherentModules_inclusion_preservesFiniteColimits X.ringCatSheaf
  constructor
  · exact fun hS => hS.map_of_exact _
  · intro hS
    let F := ObjectProperty.ι (fun M : X.Modules => M.IsCoherent)
    exact
      { exact := S.exact_of_f_is_kernel
          (isLimitOfReflects F ((KernelFork.isLimitMapConeEquiv _ _).symm hS.fIsKernel))
        mono_f := F.mono_of_mono_map hS.mono_f
        epi_g := F.epi_of_epi_map hS.epi_g }

/-- The chosen coherent conflations are exactly the ambient short exact sequences. -/
@[simp]
theorem coherentExactStructure_conflation
    (S : ShortComplex (SheafOfModules.CoherentModules X.ringCatSheaf)) :
    (coherentExactStructure X).conflation S ↔
      (S.map (ObjectProperty.ι (fun M : X.Modules => M.IsCoherent))).ShortExact :=
  coherent_shortExact_iff_map X S

/-- The literal inclusion of native coherent sheaves into all module sheaves is exact. -/
def coherentExactInclusion :
    ExactFunctor (coherentExactStructure X) (abelianExactStructure X.Modules) where
  toFunctor := ObjectProperty.ι (fun M : X.Modules => M.IsCoherent)
  map_conflation S hS := (coherent_shortExact_iff_map X S).1 hS

end AlgebraicGeometry.Scheme.Modules
