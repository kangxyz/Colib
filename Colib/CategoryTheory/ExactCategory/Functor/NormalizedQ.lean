/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.Functor.Rebase.Composition
public import Colib.CategoryTheory.ExactCategory.Functor.QIsomorphisms
public import Colib.CategoryTheory.ExactCategory.QCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Composition coherence for zero-normalized Q-functors

Canonical zero-object isomorphisms determine the normalization of the actual
Q-functors induced by exact functors. The comparison for composition has component
`eqToHom` at the distinguished vertex, with the object equality explicitly stated.
This module contains no realization or K-group map theorem.

## Implementation provenance

Extracted from `Quillen/KTheory/Map/CoherenceData.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors, specified
base isomorphisms, object equalities and component equations are retained.
Source and target share the source's object universe `u` and morphism universe `v`.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactFunctor

open CategoryTheory.ExactCategory

section ExactRebaseComposition

open scoped ZeroObject

variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  [Preadditive T] [HasFiniteBiproducts T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}

set_option backward.isDefEq.respectTransparency false in
/-- Canonical zero-object isomorphisms obey composition after passage to Q. -/
theorem comp_qZeroIso (F : ExactFunctor EC ED) (G :
  ExactFunctor ED ET) :
    ET.qIsoOfIso (F.comp G).toFunctor.mapZeroObject =
      G.mapQ.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject) ≪≫
        ET.qIsoOfIso G.toFunctor.mapZeroObject := by
  have hz : (F.comp G).toFunctor.mapZeroObject =
      G.toFunctor.mapIso F.toFunctor.mapZeroObject ≪≫ G.toFunctor.mapZeroObject := by
    apply Iso.ext
    apply Subsingleton.elim
  calc
    ET.qIsoOfIso (F.comp G).toFunctor.mapZeroObject =
        ET.qIsoOfIso (G.toFunctor.mapIso F.toFunctor.mapZeroObject ≪≫
          G.toFunctor.mapZeroObject) := congrArg ET.qIsoOfIso hz
    _ = ET.qIsoOfIso (G.toFunctor.mapIso F.toFunctor.mapZeroObject) ≪≫
        ET.qIsoOfIso G.toFunctor.mapZeroObject := ET.qIsoOfIso_trans _ _
    _ = G.mapQ.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject) ≪≫
        ET.qIsoOfIso G.toFunctor.mapZeroObject := by
      rw [CategoryTheory.ExactCategory.ExactFunctor.mapQ_qIsoOfIso]

/-- The Q-functor normalized at the chosen zero objects. This is the categorical
normalization underlying the zero-based K-map construction. -/
def normalizedQ (F : ExactFunctor EC ED) :
  EC.QCategory ⥤ ED.QCategory :=
  rebaseFunctor F.mapQ (QConstruction.of EC.deflation EC.inflation (0 : C))
    (QConstruction.of ED.deflation ED.inflation (0 : D)) (ED.qIsoOfIso F.toFunctor.mapZeroObject)

/-- The normalized Q-functor of an exact composite is the generic rebasing
of the composite Q-functor with its compositional base isomorphism. -/
theorem normalizedQ_comp_eq (F : ExactFunctor EC
  ED) (G : ExactFunctor ED ET) :
    (F.comp G).normalizedQ =
      rebaseFunctor (F.mapQ ⋙ G.mapQ) (QConstruction.of EC.deflation EC.inflation (0 : C))
        (QConstruction.of ET.deflation ET.inflation (0 : T))
        (G.mapQ.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject) ≪≫
          ET.qIsoOfIso G.toFunctor.mapZeroObject) :=
  rebaseFunctor_congr (F.mapQ_comp G) _ _ _ _ (heq_of_eq (F.comp_qZeroIso G))

/-- The comparison natural isomorphism for the actual normalized Q-functors
used by KMap. -/
def normalizedQCompIso (F : ExactFunctor EC ED) (G
  : ExactFunctor ED ET) :
    (F.comp G).normalizedQ ≅ F.normalizedQ ⋙ G.normalizedQ :=
  eqToIso (F.normalizedQ_comp_eq G) ≪≫
    rebaseFunctorCompIso F.mapQ G.mapQ
      (QConstruction.of EC.deflation EC.inflation (0 : C))
      (QConstruction.of ED.deflation ED.inflation (0 : D))
      (QConstruction.of ET.deflation ET.inflation (0 : T))
      (ED.qIsoOfIso F.toFunctor.mapZeroObject) (ET.qIsoOfIso G.toFunctor.mapZeroObject)

/-- The two normalized exact composites have equal chosen base objects. -/
theorem normalizedQCompIso_obj_base
    (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) :
    (F.comp G).normalizedQ.obj (QConstruction.of EC.deflation EC.inflation (0 : C)) =
      (F.normalizedQ ⋙ G.normalizedQ).obj (QConstruction.of EC.deflation EC.inflation (0 : C)) :=
  (congrArg (fun H : EC.QCategory ⥤ ET.QCategory =>
      H.obj (QConstruction.of EC.deflation EC.inflation (0 : C))) (F.normalizedQ_comp_eq G)).trans
    (rebaseFunctorCompIso_obj_base F.mapQ G.mapQ
      (QConstruction.of EC.deflation EC.inflation (0 : C))
      (QConstruction.of ED.deflation ED.inflation (0 : D))
      (QConstruction.of ET.deflation ET.inflation (0 : T))
      (ED.qIsoOfIso F.toFunctor.mapZeroObject) (ET.qIsoOfIso G.toFunctor.mapZeroObject))

/-- The comparison for exact functors fixes zero: its component is identity
under the equality of the chosen base objects. -/
theorem normalizedQCompIso_hom_base
    (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) :
    (F.normalizedQCompIso G).hom.app (QConstruction.of EC.deflation EC.inflation (0 : C)) =
      eqToHom (F.normalizedQCompIso_obj_base G) :=
  eqToIso_trans_hom_base (F.normalizedQ_comp_eq G) _ _ _
    (rebaseFunctorCompIso_hom_base F.mapQ G.mapQ
      (QConstruction.of EC.deflation EC.inflation (0 : C))
      (QConstruction.of ED.deflation ED.inflation (0 : D))
      (QConstruction.of ET.deflation ET.inflation (0 : T))
      (ED.qIsoOfIso F.toFunctor.mapZeroObject) (ET.qIsoOfIso G.toFunctor.mapZeroObject))

end ExactRebaseComposition

end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_tag "COL-0057",
  colib_ref "WeibelKBook" "IV, Homotopy-theoretic properties 3.2" "background"
    "Categorical comparison with a specified identity base component, not a based homotopy"]
  CategoryTheory.ExactCategory.ExactFunctor.normalizedQCompIso
  CategoryTheory.ExactCategory.ExactFunctor.normalizedQCompIso_hom_base

attribute [colib_ref "WeibelKBook"
    "IV, paragraph following Definition 6.3, induced Q-functor clause" "background"
    "Induced Q-functors motivate normalization; the explicit rebasing is a separate construction"]
  CategoryTheory.ExactCategory.ExactFunctor.normalizedQ
