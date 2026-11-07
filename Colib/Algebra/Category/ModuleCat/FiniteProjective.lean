/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Subcategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjective.lean`.

# The exact category of finite projective modules

For any ring, finite projective left modules form an extension-closed full
subcategory of modules. Its inherited conflations are precisely split short
complexes. Right modules are obtained by applying this construction to the
opposite ring; commutativity and noetherianity are not assumed.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- Finite generation and projectivity of the actual underlying module. -/
def property : ObjectProperty (ModuleCat.{v} R) :=
  fun M => Module.Finite R M ∧ Module.Projective R M

/-- The full category of finite projective left modules. -/
abbrev Category := (property.{u, v} R).FullSubcategory

instance (M : Category.{u, v} R) : Module.Finite R M.obj := M.property.1
instance (M : Category.{u, v} R) : Module.Projective R M.obj := M.property.2

instance property_isoClosed : (property.{u, v} R).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let := h.1
    let := h.2
    exact ⟨Module.Finite.equiv e.toLinearEquiv,
      Module.Projective.of_equiv e.toLinearEquiv⟩

instance property_containsZero : (property.{u, v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R (ULift.{v} PUnit),
    ModuleCat.isZero_of_subsingleton _, by constructor <;> infer_instance⟩

/-- An extension with projective quotient splits, so its middle module remains
finite projective. The splitting is proved, rather than supplied as a premise. -/
instance property_extensionClosed :
    (abelianExactStructure (ModuleCat.{v} R)).IsExtensionClosed (property R) where
  prop_middle {S} hS h₁ h₃ := by
    let := h₁.1
    let := h₁.2
    let := h₃.1
    let := h₃.2
    have h : S.ShortExact := hS
    let e := (h.splittingOfProjective.isoBinaryBiproduct ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

instance property_finiteProducts : (property.{u, v} R).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (ModuleCat.{v} R)).extensionClosed_finiteProducts (property R)

/-- The inherited exact structure, using genuine ambient short exact sequences. -/
def exactStructure : ExactStructure (Category.{u, v} R) :=
  ExactSubcategory.exactStructure (abelianExactStructure (ModuleCat.{v} R)) (property R)

/-- Every inherited conflation has an actual splitting inside the full subcategory. -/
def splittingOfConflation (S : ShortComplex (Category.{u, v} R))
    (hS : (exactStructure R).conflation S) : S.Splitting := by
  have h : (S.map (property R).ι).ShortExact := hS
  letI : Module.Projective R (S.map (property R).ι).X₃ := S.X₃.property.2
  let s := h.splittingOfProjective
  exact {
    r := (property R).homMk s.r
    s := (property R).homMk s.s
    f_r := ObjectProperty.hom_ext _ s.f_r
    s_g := ObjectProperty.hom_ext _ s.s_g
    id := ObjectProperty.hom_ext _ s.id }

/-- Conflations are exactly split short complexes, without any splitting hypothesis. -/
theorem conflation_iff_nonempty_splitting (S : ShortComplex (Category.{u, v} R)) :
    (exactStructure R).conflation S ↔ Nonempty S.Splitting := by
  constructor
  · intro hS
    exact ⟨splittingOfConflation R S hS⟩
  · rintro ⟨s⟩
    exact (s.map (property R).ι).shortExact

/-- The original full-subcategory inclusion is exact. -/
def exactInclusion : ExactFunctor (exactStructure.{u, v} R)
    (abelianExactStructure (ModuleCat.{v} R)) :=
  ExactSubcategory.exactInclusion _ _

end ModuleCat.FiniteProjective
