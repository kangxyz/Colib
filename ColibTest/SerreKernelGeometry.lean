/- Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz -/
module

public import Colib.CategoryTheory.Abelian.SerreClass.OverKernelPostcompose
public import Colib.CategoryTheory.Abelian.SerreClass.KernelPushoutMonomorphism
public import Colib.CategoryTheory.Abelian.SerreClass.ImageSubobjects

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian.SerreLocalization
open scoped ZeroObject
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
  {N M : C} (X : Over N) {U : C} (i : (overKernel N).obj X ⟶ U)

example : (overKernel N).obj X = pullback X.hom (0 : (0 : C) ⟶ N) := rfl
example : kernelPushoutObj X i = pushout (overKernelι X) i := rfl
example [Epi X.hom] : Epi (kernelPushoutMap X i) := inferInstance
example [Mono i] : Mono (kernelPushoutOverHom X i).left := inferInstance
example [Epi X.hom] : (overKernel N).map (kernelPushoutOverHom X i) =
    i ≫ (kernelPushoutIso X i).hom := kernelPushoutOverHom_kernel X i
example (j : M ⟶ N) : Over.pullback j ⋙ overKernel M ≅ overKernel N :=
  overBaseChangeKernelIso j
example (j : M ⟶ N) [Mono j] : Over.map j ⋙ overKernel N ≅ overKernel M :=
  overPostcomposeKernelIso j
example (P : ObjectProperty C) [P.IsSerreClass] (hX : P.isoModSerre X.hom) :
    P ((overKernel N).obj X) := overKernel_mem P X hX
example (P : ObjectProperty C) [P.IsSerreClass] [Epi X.hom] (hU : P U) :
    P.isoModSerre (kernelPushoutMap X i) := kernelPushoutMap_isoModSerre X i P hU
example (P : ObjectProperty C) [P.IsSerreClass] (hX : P.isoModSerre X.hom) :
    P.isoModSerre (imageSubobject X.hom).arrow :=
  imageSubobject_arrow_isoModSerre P X.hom hX
example (I : Subobject N) (hI : I ≤ imageSubobject X.hom) :
    Epi (pullback.snd X.hom I.arrow) := pullback_to_image_epi X I hI
