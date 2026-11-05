/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.GrothendieckGroup.Abelian
public import Colib.KTheory.GrothendieckGroup.Map

/-!
# Naturality of the abelian Grothendieck-group comparison

The comparison with the pinned Stacks Core Grothendieck group intertwines the
maps of an exact additive functor. The Stacks map takes explicit preservation
of short exact sequences, which follows directly from preservation of the
standard abelian conflations. No separate preservation-of-limits assumptions
are used. Both maps send the class of `X` to the class of `F.obj X` (Stacks 02MV).
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

attribute [local instance] Abelian.hasFiniteBiproducts

variable (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))

/-- The comparison intertwines exact-functor K₀ maps with the Stacks Core map,
using the functor's actual short-exact-sequence preservation proof. -/
theorem abelianGrothendieckToStacks_naturality :
    (abelianGrothendieckToStacks D).comp F.grothendieckMap =
      (CategoryTheory.GrothendieckGroup.map F.toFunctor
        (fun S hS => F.map_conflation S hS)).comp (abelianGrothendieckToStacks C) := by
  apply (abelianExactStructure C).grothendieck_hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, grothendieckMap_class,
    abelianGrothendieckToStacks_class]
  exact (CategoryTheory.GrothendieckGroup.map_of F.toFunctor
    (fun S hS => F.map_conflation S hS) X).symm

/-- Naturality expressed with the forward additive equivalences themselves. -/
theorem abelianGrothendieckEquiv_naturality :
    (abelianGrothendieckEquiv D).toAddMonoidHom.comp F.grothendieckMap =
      (CategoryTheory.GrothendieckGroup.map F.toFunctor
        (fun S hS => F.map_conflation S hS)).comp
          (abelianGrothendieckEquiv C).toAddMonoidHom := by
  apply (abelianExactStructure C).grothendieck_hom_ext
  intro X
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_coe, Function.comp_apply, grothendieckMap_class,
    abelianGrothendieckEquiv_class]
  exact (CategoryTheory.GrothendieckGroup.map_of F.toFunctor
    (fun S hS => F.map_conflation S hS) X).symm

/-- The inverse equivalences also intertwine the same exact-functor maps. -/
theorem abelianGrothendieckEquiv_symm_naturality :
    F.grothendieckMap.comp (abelianGrothendieckEquiv C).symm.toAddMonoidHom =
      (abelianGrothendieckEquiv D).symm.toAddMonoidHom.comp
        (CategoryTheory.GrothendieckGroup.map F.toFunctor
          (fun S hS => F.map_conflation S hS)) := by
  apply CategoryTheory.GrothendieckGroup.hom_ext
  intro X
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_coe, Function.comp_apply, abelianGrothendieckEquiv_symm_of,
    grothendieckMap_class]
  rw [CategoryTheory.GrothendieckGroup.map_of F.toFunctor
    (fun S hS => F.map_conflation S hS) X, abelianGrothendieckEquiv_symm_of]

end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_tag "COL-0025",
  stacks 02MV "comparison of abelian K0 maps on actual object generators",
  colib_ref "WeibelKBook" "II, paragraph 6.1.5" "comparison"
    "Naturality of the generator-preserving comparison for canonical abelian exact structures"]
  CategoryTheory.ExactCategory.ExactFunctor.abelianGrothendieckEquiv_naturality

attribute [colib_tag "COL-0025"]
  CategoryTheory.ExactCategory.ExactFunctor.abelianGrothendieckToStacks_naturality
  CategoryTheory.ExactCategory.ExactFunctor.abelianGrothendieckEquiv_symm_naturality
