/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Scheme.VectorBundle.Exact
public import Colib.CategoryTheory.ExactCategory.KernelClosed
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.AcyclicCycles

/-!
# Kernel closure of finite locally free module sheaves

In an ambient short exact sequence, finite local freeness of both the middle and quotient
terms implies finite local freeness of the kernel. This is kernel closure for the actual
inherited exact structure, not closure under arbitrary subobjects.

The mathematical input is the native Stacks theorem
`Stacks.Perfect.BoundedLocallyFreeComplexes.isFiniteLocallyFree_of_shortExact`, the
kernel step used in the proof of Stacks Tag 0FDJ. The exact-category interface is the
one migrated from Aglib at `2c34f185fa859e862661f939cd216b07bcccfb26` and used by the
scheme comparison at Quillen `c561118b`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite locally free sheaves are closed under kernels of ambient short exact sequences
whose middle and quotient terms are finite locally free. -/
instance finiteLocallyFree_isKernelClosed (X : Scheme.{u}) :
    (sheafExactStructure X).IsKernelClosed
      (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) where
  prop_kernel {S} hS h₂ h₃ :=
    Stacks.Perfect.BoundedLocallyFreeComplexes.isFiniteLocallyFree_of_shortExact S hS h₂ h₃

end AlgebraicGeometry.Scheme.Modules
