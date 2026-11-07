/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.AsSmall.Basic

/-! # Original acyclic categories and extension data under the common-universe lift

Implementation provenance:
`Quillen/Waldhausen/SmallModel/Acyclic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C]
local instance : (AsSmall.up : C ⥤ AsSmall.{0} C).IsEquivalence :=
  (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_functor
local instance : (AsSmall.down : AsSmall.{0} C ⥤ C).IsEquivalence :=
  (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_inverse

namespace Structure
variable (W : Structure C)

/-- The lifted weak class retains the original two-out-of-three property. -/
instance asSmall_twoOutOfThree [W.weq.HasTwoOutOfThreeProperty] :
    W.asSmall.weq.HasTwoOutOfThreeProperty := inferInstanceAs
  ((W.weq.inverseImage (AsSmall.down : AsSmall.{0} C ⥤ C)).HasTwoOutOfThreeProperty)

/-- The actual zero-to-object morphism lowers to the original zero-to-object morphism. -/
@[simp] theorem asSmall_zero_to_down (X : AsSmall.{0} C) :
    (W.asSmall.isZero.to_ X).down = W.isZero.to_ (AsSmall.down.obj X) := W.isZero.eq_of_src _ _


/-- The actual object-to-zero morphism is likewise unchanged after lowering. -/
@[simp] theorem asSmall_from_zero_down (X : AsSmall.{0} C) :
    (W.asSmall.isZero.from_ X).down = W.isZero.from_ (AsSmall.down.obj X) :=
        W.isZero.eq_of_tgt _ _


/-- Extension is inherited on the original cofiber diagrams after lowering. -/
theorem asSmall_extensionAxiom (he : Fibration.ExtensionAxiom W) :
    Fibration.ExtensionAxiom W.asSmall where
  extension hi hi' h h' a b c wi wq ha hc := by
    have hp := h.map (AsSmall.down : AsSmall.{0} C ⥤ C)
    have hp' := h'.map (AsSmall.down : AsSmall.{0} C ⥤ C)
    simp only [AsSmall.down_map, asSmall_zero_to_down, asSmall_from_zero_down] at hp hp'
    exact he.extension hi hi' hp hp' (AsSmall.down.map a) (AsSmall.down.map b)
      (AsSmall.down.map c) (congrArg AsSmall.down.map wi) (congrArg AsSmall.down.map wq) ha hc

/-- Lifted coarse acyclicity is the original actual predicate. -/
@[simp] theorem asSmall_acyclic_iff (X : AsSmall.{0} C) :
    Fibration.Acyclic W.asSmall X ↔ Fibration.Acyclic W (AsSmall.down.obj X) := by
  change W.weq (AsSmall.down.map (W.asSmall.isZero.to_ X)) ↔ _
  rw [AsSmall.down_map, asSmall_zero_to_down]
  rfl

end Structure
namespace Fibration
variable {W : Structure C} (N : NestedWeakEquivalences W)

/-- The original acyclic object, with only its objects and morphisms lifted. -/
def acyclicSmallUp : AcyclicCategory N ⥤ AcyclicCategory N.asSmall where
  obj X := ⟨AsSmall.up.obj X.obj, (N.coarse.asSmall_acyclic_iff _).2 X.property⟩
  map f := (acyclicObjects N.asSmall).homMk (AsSmall.up.map f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Lowering retains precisely the original coarse-acyclic witness. -/
def acyclicSmallDown : AcyclicCategory N.asSmall ⥤ AcyclicCategory N where
  obj X := ⟨AsSmall.down.obj X.obj, (N.coarse.asSmall_acyclic_iff _).1 X.property⟩
  map f := (acyclicObjects N).homMk (AsSmall.down.map f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Both functors are inverse on the original objects and arrows. -/
def acyclicSmallEquivalence : AcyclicCategory N ≌ AcyclicCategory N.asSmall where
  functor := acyclicSmallUp N
  inverse := acyclicSmallDown N
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

local instance : (acyclicSmallUp N).IsEquivalence := (acyclicSmallEquivalence
    N).isEquivalence_functor
local instance : (acyclicSmallDown N).IsEquivalence := (acyclicSmallEquivalence
    N).isEquivalence_inverse

/-- The forward equivalence retains genuine fine cofibrations and weaknesses. -/
theorem acyclicSmallUp_exact : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
    (acyclicStructure N.asSmall).cof (acyclicStructure N.asSmall).weq (acyclicSmallUp N) where
  zero h := IsZero.of_full_of_faithful_of_isZero (acyclicSmallDown N) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (acyclicSmallUp N)

/-- The inverse equivalence retains the same actual fine structure. -/
theorem acyclicSmallDown_exact : IsExact
    (acyclicStructure N.asSmall).cof (acyclicStructure N.asSmall).weq
    (acyclicStructure N).cof (acyclicStructure N).weq (acyclicSmallDown N) where
  zero h := IsZero.of_full_of_faithful_of_isZero (acyclicSmallUp N) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (acyclicSmallDown N)

/-- The actual acyclic S-constructions are isomorphic in their original maximum universe. -/
def acyclicSmallSSetIso :
    sSet (acyclicStructure N).cof (acyclicStructure N).weq ≅
      sSet (acyclicStructure N.asSmall).cof (acyclicStructure N.asSmall).weq where
  hom := {
    app _ := ↾fun A ↦ ⟨A.1 ⋙ acyclicSmallUp N, A.2.postcomp (acyclicSmallUp_exact N)⟩
    naturality _ _ _ := by ext A; rfl }
  inv := {
    app _ := ↾fun A ↦ ⟨A.1 ⋙ acyclicSmallDown N, A.2.postcomp (acyclicSmallDown_exact N)⟩
    naturality _ _ _ := by ext A; rfl }
  hom_inv_id := by ext n A : 4; apply Subtype.ext; rfl
  inv_hom_id := by ext n A : 4; apply Subtype.ext; rfl

/-- The lifted coarse/fine map is the original map in the actual lifted coordinates. -/
theorem asSmallSSetIso_changeWeak :
    sSetMap (changeWeak_exact N) ≫ N.coarse.asSmallSSetIso.hom =
      W.asSmallSSetIso.hom ≫ sSetMap (changeWeak_exact N.asSmall) := by
  ext n A : 4
  apply Subtype.ext
  rfl

/-- Original acyclic inclusions commute with the precise lifted S-construction maps. -/
theorem acyclicSmallSSetIso_inclusion :
    sSetMap (acyclicInclusion_exact N) ≫ W.asSmallSSetIso.hom =
      (acyclicSmallSSetIso N).hom ≫ sSetMap (acyclicInclusion_exact N.asSmall) := by
  ext n A : 4
  apply Subtype.ext
  rfl

/-- The same equation holds for the original coarse inclusion. -/
theorem acyclicSmallSSetIso_coarseInclusion :
    sSetMap (acyclicInclusion_coarse_exact N) ≫ N.coarse.asSmallSSetIso.hom =
      (acyclicSmallSSetIso N).hom ≫ sSetMap (acyclicInclusion_coarse_exact N.asSmall) := by
  ext n A : 4
  apply Subtype.ext
  rfl

end Fibration
end CategoryTheory.Waldhausen
