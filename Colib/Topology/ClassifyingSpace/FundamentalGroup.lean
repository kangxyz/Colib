/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.CompletionInjectivity
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# The actual fundamental group of a groupoid realization

The proved canonical groupoid-completion comparison computes all categorical
fundamental groups. For a groupoid, the original localization functor is an
equivalence by the native localization universal property. Its original map
on arrows therefore computes the fundamental group directly, in independent
object and morphism universes.

The canonical equivalences retain the realized original arrow paths and their
multiplication, including for noncommutative groups.

Implementation correspondence: the conclusions of
`Quillen/Topology/ClassifyingSpace/FundamentalGroup.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, proved here from the existing native
completion comparison rather than repeating the point-comma argument.
-/
@[expose] public noncomputable section

universe u v
open CategoryTheory

namespace CategoryTheory.GroupoidClassifying

variable {C : Type u} [Category.{v} C] [IsGroupoid C]

/-- The original realized-arrow homomorphism computes the actual fundamental group. -/
theorem fundamentalGroupMap_bijective_general (c : C) :
    Function.Bijective ((classifyingFundamentalGroupoidFunctor C).mapEnd c) := by
  let W : MorphismProperty C := ⊤
  let : (𝟭 C).IsLocalization W := Functor.IsLocalization.for_id W (by
    intro X Y f _
    infer_instance)
  let e := Localization.uniq (𝟭 C) W.Q W
  let : e.functor.IsEquivalence := e.isEquivalence_functor
  let : W.Q.IsEquivalence := Functor.isEquivalence_of_iso
    (Localization.compUniqFunctor (𝟭 C) W.Q W)
  have hq : Function.Bijective (W.Q.mapEnd c) :=
    ⟨fun _ _ h ↦ End.ext (W.Q.map_injective (congrArg End.asHom h)), fun g ↦ by
      obtain ⟨f, hf⟩ := W.Q.map_surjective g.asHom
      exact ⟨End.of f, End.ext hf⟩⟩
  have h := (classifyingGroupoidCompletionMap_bijective C c).comp hq
  have he : (classifyingFundamentalGroupoidFunctor C).mapEnd c =
      (classifyingGroupoidCompletionMap C c).comp (W.Q.mapEnd c) := by
    apply MonoidHom.ext
    intro g
    apply End.ext
    exact eq_of_heq
      (Functor.hcongr_hom (toClassifyingGroupoidCompletionFunctor C) g.asHom).symm
  rw [he]
  exact h

/-- The actual realized-arrow homomorphism as a multiplicative equivalence. -/
def fundamentalGroupEquiv (c : C) :
    End c ≃* FundamentalGroup (ClassifyingSpace C) (classifyingSpacePoint c) :=
  MulEquiv.ofBijective ((classifyingFundamentalGroupoidFunctor C).mapEnd c)
    (fundamentalGroupMap_bijective_general c)

@[simp] lemma fundamentalGroupEquiv_apply (c : C) (g : End c) :
    fundamentalGroupEquiv c g =
      FundamentalGroup.fromPath ⟦classifyingSpacePath g.asHom⟧ := rfl

/-- The original group is the fundamental group of its actual one-object nerve realization. -/
def singleObjFundamentalGroupEquiv (G : Type u) [Group G] :
    G ≃* FundamentalGroup (ClassifyingSpace (SingleObj G))
      (classifyingSpacePoint (SingleObj.star G)) :=
  (SingleObj.toEnd G).trans (fundamentalGroupEquiv (SingleObj.star G))

/-- Original group elements give their original degree-one homotopy classes. -/
def singleObjPiOneEquiv (G : Type u) [Group G] :
    G ≃* HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj G))
      (classifyingSpacePoint (SingleObj.star G)) :=
  (singleObjFundamentalGroupEquiv G).trans HomotopyGroup.pi1MulEquivFundamentalGroup.symm

@[simp] lemma singleObjPiOneEquiv_apply (G : Type u) [Group G] (g : G) :
    singleObjPiOneEquiv G g = HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (FundamentalGroup.fromPath
        ⟦classifyingSpacePath (SingleObj.toEnd G g).asHom⟧) := rfl

end CategoryTheory.GroupoidClassifying
