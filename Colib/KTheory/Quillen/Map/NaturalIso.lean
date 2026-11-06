/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Map.Functoriality
public import Colib.CategoryTheory.Functor.Rebase.NaturalIso
public import Colib.CategoryTheory.ExactCategory.Functor.QNaturalIso

/-! # Natural-isomorphism invariance of the canonical Quillen K-map

Adapted from `Quillen/KTheory/Map/NaturalIso.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors,
canonical zero isomorphisms and based homotopies.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe v u v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}
  {F G : ExactFunctor EC ED}

/-- The Q comparison respects the canonical zero-object isomorphisms, since
maps to the original zero object are unique. -/
theorem mapQIso_comp_qZeroIso (e : F.toFunctor ≅ G.toFunctor) :
    (mapQIso e).app (QConstruction.of EC.deflation EC.inflation (0 : C)) ≪≫
      ED.qIsoOfIso G.toFunctor.mapZeroObject = ED.qIsoOfIso F.toFunctor.mapZeroObject := by
  rw [mapQIso_app, ← CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans]
  congr 1
  apply Iso.ext
  apply Subsingleton.elim

/-- The natural comparison of the actual zero-normalized Q-functors used in
`KMap`, rather than an unbased comparison of classifying maps. -/
def normalizedQIso (e : F.toFunctor ≅ G.toFunctor) : F.normalizedQ ≅ G.normalizedQ :=
  rebaseFunctorNatIso (mapQIso e) (QConstruction.of EC.deflation EC.inflation (0 : C))
    (QConstruction.of ED.deflation ED.inflation (0 : D))
    (ED.qIsoOfIso F.toFunctor.mapZeroObject) (ED.qIsoOfIso G.toFunctor.mapZeroObject)

/-- Both normalized Q-functors send the source zero to the same target zero. -/
theorem normalizedQIso_obj_base :
    F.normalizedQ.obj (QConstruction.of EC.deflation EC.inflation (0 : C)) =
      G.normalizedQ.obj (QConstruction.of EC.deflation EC.inflation (0 : C)) :=
  rebaseFunctorNatIso_obj_base _ _ _ _

/-- The normalized comparison is the identity at the chosen zero vertex. -/
theorem normalizedQIso_hom_base (e : F.toFunctor ≅ G.toFunctor) :
    (normalizedQIso e).hom.app (QConstruction.of EC.deflation EC.inflation (0 : C)) =
      eqToHom (normalizedQIso_obj_base (F := F) (G := G)) :=
  rebaseFunctorNatIso_hom_base _ _ _ _ _ (mapQIso_comp_qZeroIso e)

/-- Naturally isomorphic exact functors induce the same canonical K-map.
The comparison realizes to a genuine homotopy fixed at the chosen zero point. -/
theorem KMap_eq_of_natIso (e : F.toFunctor ≅ G.toFunctor) (n : ℕ) :
    F.KMap n = G.KMap n := by
  let H := classifyingSpaceNaturalTransformationBasedHomotopy
    (normalizedQIso e).hom (QConstruction.of EC.deflation EC.inflation (0 : C))
    (normalizedQIso_obj_base (F := F) (G := G)) (normalizedQIso_hom_base e)
  have hH : ∀ t, H.toHomotopy (t, EC.kBasepoint) = ED.kBasepoint := by
    intro t
    exact (H.prop t EC.kBasepoint (Set.mem_singleton _)).trans F.normalizedQ_map_point
  exact HomotopyGroup.piMap_eq_of_based_homotopy n F.normalizedQ_map_point G.normalizedQ_map_point
    H.toHomotopy hH

end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_ref "quillen" "Quillen/KTheory/Map/NaturalIso.lean"
  "adaptation" "Canonical K-map invariance through a genuinely zero-fixed homotopy"]
  CategoryTheory.ExactCategory.ExactFunctor.KMap_eq_of_natIso
