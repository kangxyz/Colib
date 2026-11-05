/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.CategoryTheory.Groupoid.Subgroupoid

/-!
# The transported image of a groupoid-valued functor

Specified isomorphisms from chosen image objects transport the image arrows to
all target objects. Membership retains the actual conjugation by these isomorphisms.


## Implementation provenance

Extracted from `Quillen/Topology/Realization/EdgePathPresentation/OpenCoverFull.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
universes, maps and hypotheses are retained.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Set

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Groupoids

variable {A : Type u} {G : Type v} [Groupoid A] [Groupoid G]

/-- The image of a groupoid-valued functor, transported to all target objects
by specified isomorphisms. -/
def CategoryTheory.transportedImageSubgroupoid (F : A ⥤ G) (a : G → A)
    (e : ∀ x, F.obj (a x) ≅ x) : Subgroupoid G where
  arrows x y := {p | ∃ q : a x ⟶ a y, F.map q = (e x).hom ≫ p ≫ (e y).inv}
  inv := by
    rintro x y p ⟨q, hq⟩
    refine ⟨inv q, ?_⟩
    rw [F.map_inv]
    simpa [Category.assoc, Groupoid.inv_eq_inv] using congrArg Groupoid.inv hq
  mul := by
    rintro x y z p ⟨q, hq⟩ r ⟨s, hs⟩
    refine ⟨q ≫ s, ?_⟩
    rw [F.map_comp, hq, hs]
    simp [Category.assoc]

end Groupoids

attribute [colib_tag "COL-0096",
  colib_ref "HatcherAT" "Section 1.1, Proposition 1.5 and preceding construction, page 28"
    "background"
    "Transport by chosen endpoint isomorphisms, not a literal groupoid-image theorem"]
  CategoryTheory.transportedImageSubgroupoid
