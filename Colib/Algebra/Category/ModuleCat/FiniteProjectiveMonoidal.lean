/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveComplement
public import Colib.CategoryTheory.Monoidal.Core
public import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts

/-!
Implementation provenance:
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveMonoidal.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The direct-sum monoidal groupoid of finite projective modules

The isomorphism groupoid is mathlib's actual categorical core. The monoidal
operation is the chosen coproduct, canonically isomorphic to the biproduct;
its unit is the chosen initial object, hence a zero object. These structures
are named definitions, not global instances: they do not select a tensor-product
monoidal structure or compete with another monoidal structure on modules.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- The direct-sum monoidal structure on finite projective modules. -/
@[instance_reducible]
def categoryDirectSumMonoidal : MonoidalCategory (Category.{u, u} R) :=
  monoidalOfHasFiniteCoproducts _

attribute [local instance] categoryDirectSumMonoidal

/-- The direct-sum symmetry is inherited from the actual coproduct braiding. -/
@[instance_reducible]
def categoryDirectSumSymmetric : SymmetricCategory (Category.{u, u} R) :=
  symmetricOfHasFiniteCoproducts _

attribute [local instance] categoryDirectSumSymmetric

/-- Finite projective modules with all their original isomorphisms. -/
abbrev IsoCategory := Core (Category.{u, u} R)

/-- Direct sum on the actual isomorphism groupoid. -/
@[instance_reducible]
def directSumMonoidal : MonoidalCategory (IsoCategory R) := inferInstance

attribute [local instance] directSumMonoidal

/-- Direct sum is symmetric, with no strict associativity assumption. -/
@[instance_reducible]
def directSumSymmetric : SymmetricCategory (IsoCategory R) := inferInstance

/-- A finite free module as an object of the actual isomorphism groupoid. -/
def freeIso (n : ℕ) : IsoCategory R := ⟨free n⟩

/-- Cofinality of finite free modules retains an actual complementary projective
object and an actual isomorphism in the core. -/
theorem exists_complement_iso_freeIso (P : IsoCategory R) :
    ∃ (n : ℕ) (Q : IsoCategory R), Nonempty (P ⊗ Q ≅ freeIso R n) := by
  obtain ⟨n, Q, ⟨e⟩⟩ := exists_complement_iso_free P.of
  refine ⟨n, ⟨Q⟩, ⟨Core.isoMk ?_⟩⟩
  exact (biprod.isoCoprod P.of Q).symm ≪≫ e

/-- Rank zero agrees with the actual monoidal unit by its universal property. -/
def freeIsoZero : (𝟙_ (IsoCategory R)) ≅ freeIso R 0 :=
  Core.isoMk (initialIsInitial.uniqueUpToIso (free_zero_isZero (R := R)).isInitial)

/-- The specified rank-one free object generates the labelled free sequence. -/
def freeIsoSucc (n : ℕ) : freeIso R 1 ⊗ freeIso R n ≅ freeIso R (n + 1) :=
  Core.isoMk ((biprod.isoCoprod (free 1) (free n)).symm ≪≫ freeSuccIso n)

/-- Iterated direct sum of the actual rank-one object, with its chosen unit at zero. -/
def rankOnePower : ℕ → IsoCategory R
  | 0 => 𝟙_ (IsoCategory R)
  | n + 1 => freeIso R 1 ⊗ rankOnePower n

/-- Iterated sums of the rank-one free module are explicitly the labelled free modules. -/
def rankOnePowerIsoFree : ∀ n, rankOnePower R n ≅ freeIso R n
  | 0 => freeIsoZero R
  | n + 1 => (Iso.refl _ ⊗ᵢ rankOnePowerIsoFree n) ≪≫ freeIsoSucc R n

/-- Every finite projective object admits a complementary projective summand
whose sum is a power of the rank-one object. No rank cancellation is used. -/
theorem rankOne_cofinal (P : IsoCategory R) :
    ∃ (n : ℕ) (Q : IsoCategory R), Nonempty (P ⊗ Q ≅ rankOnePower R n) := by
  obtain ⟨n, Q, ⟨e⟩⟩ := exists_complement_iso_freeIso R P
  exact ⟨n, Q, ⟨e ≪≫ (rankOnePowerIsoFree R n).symm⟩⟩

/-- Left direct-sum translation is faithful on the original isomorphisms. -/
theorem directSumLeft_faithful (P : IsoCategory R) : (tensorLeft P).Faithful where
  map_injective {X Y} {f g} h := by
    apply Core.hom_ext
    have h' := congrArg (fun k => k.iso.hom) h
    change coprod.map (𝟙 P.of) f.iso.hom = coprod.map (𝟙 P.of) g.iso.hom at h'
    have h'' := congrArg (fun k => (coprod.inr : X.of ⟶ P.of ⨿ X.of) ≫ k ≫
      coprod.desc (0 : P.of ⟶ Y.of) (𝟙 Y.of)) h'
    simpa only [Category.assoc, coprod.inr_map_assoc, coprod.inr_desc, Category.comp_id]
      using h''

/-- Right direct-sum translation is faithful on the original isomorphisms. -/
theorem directSumRight_faithful (P : IsoCategory R) : (tensorRight P).Faithful where
  map_injective {X Y} {f g} h := by
    apply Core.hom_ext
    have h' := congrArg (fun k => k.iso.hom) h
    change coprod.map f.iso.hom (𝟙 P.of) = coprod.map g.iso.hom (𝟙 P.of) at h'
    have h'' := congrArg (fun k => (coprod.inl : X.of ⟶ X.of ⨿ P.of) ≫ k ≫
      coprod.desc (𝟙 Y.of) (0 : P.of ⟶ Y.of)) h'
    simpa only [Category.assoc, coprod.inl_map_assoc, coprod.inl_desc, Category.comp_id]
      using h''

end ModuleCat.FiniteProjective
