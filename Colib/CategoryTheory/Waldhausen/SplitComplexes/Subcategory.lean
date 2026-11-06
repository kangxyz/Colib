/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Pushouts
public import Colib.Algebra.Homology.CochainComplex.DegreewiseSplitMono
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.Basic
public import Colib.CategoryTheory.Waldhausen.SubcategoryInclusion

/-!
# Degreewise split Waldhausen subcategories of complexes

For a replete extension-closed full subcategory containing zero, retain
exactly the inherited cofibrations which split in every degree. Thus the
quotient must still lie in the chosen subcategory. All Waldhausen axioms
are derived from the ambient pushout and quasi-isomorphism gluing theorems.
The identity comparison to the ambient-monomorphism convention and
inclusions between such subcategories are actual exact functors.
-/
/-! Adapted from `Quillen.Waldhausen.SplitComplexes.Subcategory`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- Inherited cofibrations with termwise splittings. The inherited condition
requires that the actual quotient belong to the full subcategory. -/
def splitSubcategoryCofibrations : MorphismProperty P.FullSubcategory :=
  subcategoryCofibrations P ⊓ CochainComplex.degreewiseSplitMono.inverseImage P.ι

/-- The degreewise split, quasi-isomorphism Waldhausen structure on an actual
extension-closed full subcategory of complexes. -/
def splitComplexSubcategory : Structure P.FullSubcategory :=
  { complexSubcategory P with
    cof := splitSubcategoryCofibrations P
    cof_multiplicative := by
      let : (subcategoryCofibrations P).IsMultiplicative :=
        (complexSubcategory P).cof_multiplicative
      unfold splitSubcategoryCofibrations
      infer_instance
    cof_iso := by
      intro K L f hf
      let : IsIso f := hf
      exact ⟨(complexSubcategory P).cof_iso f hf, degreewiseSplitMono_of_isIso f.hom⟩
    cof_zero K := ⟨(complexSubcategory P).cof_zero K,
      degreewiseSplitMono_of_isZero (P.ι.map_isZero (complexSubcategory P).isZero) _⟩
    pushout_exists i f hi := (complexSubcategory P).pushout_exists i f hi.1
    cof_pushout hi h := ⟨(complexSubcategory P).cof_pushout hi.1 h,
      degreewiseSplitMono_pushout hi.2 ((ExactSubcategory.exactInclusion (abelianExactStructure
        (CochainComplex A ℤ)) P).map_isPushout hi.1 h)⟩
    gluing a b d p hi hi' h h' ei ef eg ej ha hb hd :=
      (complexSubcategory P).gluing a b d p hi.1 hi'.1 h h' ei ef eg ej ha hb hd }

/-- The canonical identity comparison changes only the cofibration convention. -/
theorem splitComplexSubcategory_to_complexSubcategory_exact :
    IsExact (splitComplexSubcategory P).cof (splitComplexSubcategory P).weq
      (complexSubcategory P).cof (complexSubcategory P).weq (𝟭 P.FullSubcategory) where
  zero h := h
  cofibration _ h := h.1
  weak _ h := h
  pushout _ h := h

/-- The actual full inclusion into all complexes with split cofibrations. -/
theorem splitComplexSubcategory_inclusion_exact :
    IsExact (splitComplexSubcategory P).cof (splitComplexSubcategory P).weq
      (splitComplexes A).cof (splitComplexes A).weq P.ι where
  zero h := P.ι.map_isZero h
  cofibration _ h := h.2
  weak _ h := h
  pushout hi h := (ExactSubcategory.exactInclusion (abelianExactStructure (CochainComplex A ℤ))
    P).map_isPushout hi.1 h

variable (Q : ObjectProperty (CochainComplex A ℤ))
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts] (h : P ≤ Q)

/-- Inclusion of object properties preserves split cofibrations, actual
quasi-isomorphisms, and the required pushouts. -/
theorem splitSubcategoryInclusion_exact :
    IsExact (splitComplexSubcategory P).cof (splitComplexSubcategory P).weq
      (splitComplexSubcategory Q).cof (splitComplexSubcategory Q).weq
      (ObjectProperty.ιOfLE h) where
  zero hZ := (ObjectProperty.ιOfLE h).map_isZero hZ
  cofibration f hf := ⟨(subcategoryInclusion_exact P Q h).cofibration f hf.1, hf.2⟩
  weak _ hf := hf
  pushout hi hs := (subcategoryInclusion_exact P Q h).pushout hi.1 hs

end CategoryTheory.Waldhausen
