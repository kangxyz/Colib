/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Abelian.Devissage.Layers
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Ordinary functors on supported subquotient layers

Restriction, enlargement and inclusion retain their original ordered endpoints,
natural maps and unit isomorphism. The diagonal layer supplies the actual
terminal zero-supported object, and top support is an ordinary equivalence.


## Implementation provenance

Adapted from
`Quillen/Aglib/CategoryTheory/ExactCategory/Filtration/LayerFunctors.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and independent object/hom universes
are retained. No extension-closure assumption or Resolution structure is used.
The source `Quillen.Devissage` namespace is now
`CategoryTheory.Abelian.Devissage`; no K-theory dependency is introduced.
-/
@[expose] public section

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory.Abelian.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts]

namespace Layer
variable {P} {M : C}

/-- Inclusion of layers supported in a smaller subobject. -/
def supportedInclusion {A N : Subobject M} (hAN : A ≤ N) :
    Supported (P := P) A ⥤ Supported (P := P) N :=
  (show Monotone (fun L : Supported (P := P) A =>
    (⟨L.val, L.property.trans hAN⟩ : Supported (P := P) N)) from
    fun _ _ h => h).functor

/-- Intersect a supported layer with the smaller ambient subobject. -/
def supportedRestriction (A N : Subobject M) :
    Supported (P := P) N ⥤ Supported (P := P) A :=
  (show Monotone (fun L : Supported (P := P) N =>
    (⟨restrict A L.val, inf_le_right⟩ : Supported (P := P) A)) from
    fun _ _ h => restrict_mono A h).functor

/-- The intermediate enlargement functor appearing in the contraction zigzag. -/
def supportedEnlargement {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    Supported (P := P) N ⥤ Supported (P := P) N :=
  (enlarge_mono hAN hA).functor

/-- Restricting a layer already supported in `A` does nothing. -/
def supportedRestrictionUnit {A N : Subobject M} (hAN : A ≤ N) :
    supportedInclusion (P := P) hAN ⋙ supportedRestriction A N ≅
      𝟭 (Supported (P := P) A) :=
  NatIso.ofComponents (fun L => eqToIso (by
    apply Subtype.ext
    apply Layer.ext
    · exact inf_eq_left.mpr (L.val.le.trans L.property)
    · exact inf_eq_left.mpr L.property)) (by intros; apply Subsingleton.elim)

/-- The restricted layer maps into the intermediate enlargement. -/
def supportedRestrictionToEnlargement {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    supportedRestriction (P := P) A N ⋙ supportedInclusion hAN ⟶
      supportedEnlargement hAN hA where
  app L := homOfLE ⟨le_rfl, inf_le_left⟩

/-- The original layer maps into the same intermediate enlargement. -/
def supportedIdToEnlargement {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    𝟭 (Supported (P := P) N) ⟶ supportedEnlargement hAN hA where
  app L := homOfLE ⟨inf_le_left, le_rfl⟩

/-- The degenerate layer with both endpoints equal. -/
def diagonal (N : Subobject M) : Layer P M where
  lower := N
  upper := N
  le := le_rfl
  property := by
    have h : Subobject.ofLE N N le_rfl = 𝟙 (N : C) := by simp
    rw [h]
    exact P.prop_of_isZero (isZero_cokernel_of_epi (𝟙 (N : C)))

/-- The zero-supported layer category has a terminal object. -/
def supportedBottomIsTerminal :
    IsTerminal (⟨diagonal (P := P) (⊥ : Subobject M), le_rfl⟩ : Supported (P := P) ⊥) :=
  IsTerminal.ofUniqueHom (fun L => homOfLE ⟨bot_le, L.property⟩)
    (by intros; apply Subsingleton.elim)

/-- Supporting layers in the maximal subobject imposes no restriction. -/
def supportedTopEquivalence : Supported (P := P) (⊤ : Subobject M) ≌ Layer P M where
  functor :=
    { obj := fun L => L.val
      map := fun f => homOfLE (leOfHom f) }
  inverse :=
    { obj := fun L => ⟨L, le_top⟩
      map := fun f => homOfLE (leOfHom f) }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply Subsingleton.elim)

end Layer
end CategoryTheory.Abelian.Devissage
