/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Subcategory
public import Colib.CategoryTheory.ExactCategory.Functor.Pushouts
public import Colib.CategoryTheory.Waldhausen.Complexes
public import Colib.CategoryTheory.Waldhausen.ExactCategory
public import Colib.KTheory.Waldhausen.Map
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Colib.CategoryTheory.ExactCategory.Abelian

/-!
# Extension-closed subcategories of complexes

An actual replete, extension-closed full subcategory of complexes containing
zero inherits a Waldhausen structure. Its cofibrations are ambient short
exact sequences whose quotient remains in the subcategory; its weak
equivalences are ambient quasi-isomorphisms. All Waldhausen axioms, including
gluing, are derived. Applications must prove the object-property closure
hypotheses, rather than supplying any K-theory comparison or localization.


Implementation provenance:
`Quillen/Waldhausen/ComplexSubcategory.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory.Waldhausen

section Complexes

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The inherited exact structure is used only for its actual cofibrations. -/
abbrev subcategoryCofibrations : MorphismProperty P.FullSubcategory :=
  (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A ℤ)) P).inflation

/-- Weak equivalences in the full subcategory are genuine quasi-isomorphisms. -/
abbrev subcategoryWeakEquivalences : MorphismProperty P.FullSubcategory :=
  (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι

/-- The full Waldhausen structure is proved from the closure properties of
actual complexes. No K-theory theorem is an input. -/
def complexSubcategory : Structure P.FullSubcategory :=
  { ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P) with
    weq := subcategoryWeakEquivalences P
    weq_multiplicative := inferInstance
    weq_iso := by
      intro X Y f hf
      let : IsIso f := hf
      change QuasiIso f.hom
      infer_instance
    gluing := by
      intro B D E T B' D' E' T' i f g j i' f' g' j' a b d p hi hi' h h' ei ef eg ej ha hb hd
      have hiA := (ExactSubcategory.exactInclusion
        (abelianExactStructure (CochainComplex A ℤ)) P).map_inflation i hi
      have hiA' := (ExactSubcategory.exactInclusion
        (abelianExactStructure (CochainComplex A ℤ)) P).map_inflation i' hi'
      let : Mono i.hom := (abelianExactStructure_inflation_iff _ _).1 hiA
      let : Mono i'.hom := (abelianExactStructure_inflation_iff _ _).1 hiA'
      let : QuasiIso a.hom := ha
      let : QuasiIso b.hom := hb
      let : QuasiIso d.hom := hd
      have hA : IsPushout i.hom f.hom g.hom j.hom :=
        (ExactSubcategory.exactInclusion _ P).map_isPushout hi h
      have hA' : IsPushout i'.hom f'.hom g'.hom j'.hom :=
        (ExactSubcategory.exactInclusion _ P).map_isPushout hi' h'
      exact CochainComplex.quasiIso_gluing hA hA'
        a.hom b.hom d.hom p.hom
        (congrArg (fun k ↦ k.hom) ei) (congrArg (fun k ↦ k.hom) ef)
        (congrArg (fun k ↦ k.hom) eg) (congrArg (fun k ↦ k.hom) ej) }

/-- The actual inclusion of complexes is Waldhausen-exact. -/
theorem complexSubcategory_inclusion_exact :
    IsExact (complexSubcategory P).cof (complexSubcategory P).weq
      (complexes A).cof (complexes A).weq P.ι where
  zero h := P.ι.map_isZero h
  cofibration f hf := (abelianExactStructure_inflation_iff _ _).1
    ((ExactSubcategory.exactInclusion _ P).map_inflation f hf)
  weak _ hf := hf
  pushout hi h := (ExactSubcategory.exactInclusion _ P).map_isPushout hi h

end Complexes

end CategoryTheory.Waldhausen
