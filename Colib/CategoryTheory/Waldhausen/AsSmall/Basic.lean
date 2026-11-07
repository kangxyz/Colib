/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory


/-!
# The Waldhausen structure on Mathlib AsSmall

`AsSmall` lifts objects and homs into their original maximum universe. Both
morphism classes are pulled back from the original category. The actual
S-constructions are simplicially isomorphic by exact up/down postcomposition.


Implementation provenance:
`Quillen/Waldhausen/SmallModel/Basic.lean`
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

local instance smallUp_isEquivalence : (AsSmall.up : C ⥤ AsSmall.{0} C).IsEquivalence :=
  (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_functor
local instance smallDown_isEquivalence : (AsSmall.down : AsSmall.{0} C ⥤ C).IsEquivalence :=
  (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_inverse

namespace Structure
variable (W : Structure C)

/-- The chosen zero and original classes on the actual lifted small category. -/
def asSmall : Structure (AsSmall.{0} C) where
  zero := AsSmall.up.obj W.zero
  isZero := IsZero.of_full_of_faithful_of_isZero (AsSmall.down : AsSmall.{0} C ⥤ C) _ W.isZero
  cof := W.cof.inverseImage AsSmall.down
  weq := W.weq.inverseImage AsSmall.down
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact W.cof_iso _ (inferInstance : IsIso (AsSmall.down.map f))
  weq_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact W.weq_iso _ (inferInstance : IsIso (AsSmall.down.map f))
  cof_zero := by
    intro X
    change W.cof _
    convert W.cof_zero (AsSmall.down.obj X) using 1
    all_goals first | rfl | exact W.isZero.eq_of_src _ _
  pushout_exists := by
    intro A B D i f hi
    obtain ⟨P,g,j,h⟩ := W.pushout_exists (AsSmall.down.map i) (AsSmall.down.map f) hi
    exact ⟨AsSmall.up.obj P, AsSmall.up.map g, AsSmall.up.map j, h.map AsSmall.up⟩
  cof_pushout := by
    intro A B D P i f g j hi h
    exact W.cof_pushout hi (h.map AsSmall.down)
  gluing := by
    intro A B D P A' B' D' P' i f g j i' f' g' j' a b d p hi hi' h h' ei ef eg ej ha hb hd
    exact W.gluing (AsSmall.down.map a) (AsSmall.down.map b) (AsSmall.down.map d)
      (AsSmall.down.map p) hi hi' (h.map AsSmall.down) (h'.map AsSmall.down)
      (congrArg AsSmall.down.map ei) (congrArg AsSmall.down.map ef)
      (congrArg AsSmall.down.map eg) (congrArg AsSmall.down.map ej) ha hb hd

/-- Lifting preserves the original classes and all genuine pushout squares. -/
theorem asSmall_up_exact :
    IsExact W.cof W.weq W.asSmall.cof W.asSmall.weq (AsSmall.up : C ⥤ AsSmall.{0} C) where
  zero h := IsZero.of_full_of_faithful_of_isZero AsSmall.down _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map AsSmall.up

/-- Lowering forgets only the universe lifts. -/
theorem asSmall_down_exact :
    IsExact W.asSmall.cof W.asSmall.weq W.cof W.weq (AsSmall.down : AsSmall.{0} C ⥤ C) where
  zero h := IsZero.of_full_of_faithful_of_isZero (AsSmall.up : C ⥤ AsSmall.{0} C) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map AsSmall.down

/-- The actual S-constructions lie in the same `max u v` universe and are
strictly inverse under exact up/down postcomposition. -/
def asSmallSSetIso : sSet W.cof W.weq ≅ sSet W.asSmall.cof W.asSmall.weq where
  hom := {
    app _ := ↾fun A ↦ ⟨A.1 ⋙ AsSmall.up, A.2.postcomp W.asSmall_up_exact⟩
    naturality _ _ _ := by ext A; rfl }
  inv := {
    app _ := ↾fun A ↦ ⟨A.1 ⋙ AsSmall.down, A.2.postcomp W.asSmall_down_exact⟩
    naturality _ _ _ := by ext A; rfl }
  hom_inv_id := by
    ext n A : 4
    apply Subtype.ext
    rfl
  inv_hom_id := by
    ext n A : 4
    apply Subtype.ext
    rfl

end Structure

section Functoriality
variable {D : Type u} [Category.{v} D] {W : Structure C} {W' : Structure D}
  {F : C ⥤ D}

/-- The actual lifted functor keeps the original object and morphism map. -/
def asSmallFunctor (F : C ⥤ D) : AsSmall.{0} C ⥤ AsSmall.{0} D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- Genuine exactness survives lifting both universes. -/
theorem IsExact.asSmall (hF : IsExact W.cof W.weq W'.cof W'.weq F) :
    IsExact W.asSmall.cof W.asSmall.weq W'.asSmall.cof W'.asSmall.weq
      (asSmallFunctor F) :=
  W.asSmall_down_exact.comp (hF.comp W'.asSmall_up_exact)

/-- Original S-maps commute strictly with the actual universe-lifting isomorphisms. -/
theorem asSmallSSetIso_naturality (hF : IsExact W.cof W.weq W'.cof W'.weq F) :
    sSetMap hF ≫ W'.asSmallSSetIso.hom =
      W.asSmallSSetIso.hom ≫ sSetMap hF.asSmall := by
  ext n A : 4
  apply Subtype.ext
  rfl

end Functoriality
namespace Fibration.NestedWeakEquivalences
variable {W : Structure C} (N : NestedWeakEquivalences W)

/-- Both lifted weak models retain the same actual cofibrations and chosen zero. -/
def asSmall : NestedWeakEquivalences W.asSmall where
  coarse := N.coarse.asSmall
  cof_eq := by change N.coarse.cof.inverseImage _ = W.cof.inverseImage _; rw [N.cof_eq]
  zero_eq := congrArg AsSmall.up.obj N.zero_eq
  le_weq := fun _ _ f hf ↦ N.le_weq (AsSmall.down.map f) hf

end Fibration.NestedWeakEquivalences
end CategoryTheory.Waldhausen
