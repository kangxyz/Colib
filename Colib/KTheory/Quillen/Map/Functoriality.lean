/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Quillen.Map.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.NormalizedQ
public import Colib.Topology.Homotopy.HomotopyGroup.BasedHomotopy
public import Colib.Topology.Realization.HomotopyBridge

/-!
# Composition of the actual zero-based Quillen K-group maps

The normalized Q-functor comparison has the prescribed `eqToHom` component at
zero. The realized natural-transformation homotopy is therefore fixed at that
vertex. Based homotopy invariance gives the composition law for the original
KMap, whose identification with the induced homotopy-group map is definitional.

## Implementation provenance

Adapted from `Quillen/KTheory/Map/Functoriality.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. All three source declarations retain
their actual normalized functors, canonical zero-object maps, basepoints,
shared source/target universes, degree shift and composition orientation.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  [Preadditive T] [HasFiniteBiproducts T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}

/-- Realization of the normalized Q-functor preserves the chosen K-space points. -/
theorem normalizedQ_map_point (F : ExactFunctor EC ED) :
    classifyingSpaceMap F.normalizedQ EC.kBasepoint = ED.kBasepoint :=
  rebaseFunctor_map_point F.mapQ (QConstruction.of EC.deflation EC.inflation (0 : C))
    (QConstruction.of ED.deflation ED.inflation (0 : D)) (ED.qIsoOfIso F.toFunctor.mapZeroObject)

/-- The original K-map is definitionally induced by the normalized Q-functor. -/
theorem KMap_eq_piMap (F : ExactFunctor EC ED) (n : ℕ) :
    F.KMap n = HomotopyGroup.piMap n (classifyingSpaceMap F.normalizedQ).hom
      F.normalizedQ_map_point := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact functor composition is respected by all genuine zero-based Quillen
K-group homomorphisms. The proof uses a continuous homotopy fixed at zero. -/
@[simp]
theorem KMap_comp (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) (n : ℕ) :
    (F.comp G).KMap n = (G.KMap n).comp (F.KMap n) := by
  let H := classifyingSpaceNaturalTransformationBasedHomotopy
    (F.normalizedQCompIso G).hom (QConstruction.of EC.deflation EC.inflation (0 : C))
    (F.normalizedQCompIso_obj_base G) (F.normalizedQCompIso_hom_base G)
  have hcomp : classifyingSpaceMap (F.normalizedQ ⋙ G.normalizedQ) EC.kBasepoint =
      ET.kBasepoint := by
    rw [classifyingSpaceMap_comp, TopCat.comp_app, F.normalizedQ_map_point,
      G.normalizedQ_map_point]
  have hH : ∀ t, H.toHomotopy (t, EC.kBasepoint) = ET.kBasepoint := by
    intro t
    exact (H.prop t EC.kBasepoint (Set.mem_singleton _)).trans
      (F.comp G).normalizedQ_map_point
  have hmap := HomotopyGroup.piMap_eq_of_based_homotopy n
    (F.comp G).normalizedQ_map_point hcomp H.toHomotopy hH
  calc
    (F.comp G).KMap n =
        HomotopyGroup.piMap n (classifyingSpaceMap (F.normalizedQ ⋙ G.normalizedQ)).hom
          hcomp := hmap
    _ = (G.KMap n).comp (F.KMap n) := by
      apply MonoidHom.ext
      intro a
      change HomotopyGroup.map (classifyingSpaceMap (F.normalizedQ ⋙ G.normalizedQ)).hom
        hcomp a = HomotopyGroup.map (classifyingSpaceMap G.normalizedQ).hom
          G.normalizedQ_map_point
          (HomotopyGroup.map (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point a)
      simp only [classifyingSpaceMap_comp, TopCat.hom_comp]
      exact HomotopyGroup.map_comp _ _ _ _ a

end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_tag "COL-0072",
  colib_ref "WeibelKBook" "IV, functoriality paragraph following Definition 6.3, page 54"
    "adaptation" "Composition of the actual zero-based K-group maps induced by exact functors"]
  CategoryTheory.ExactCategory.ExactFunctor.KMap_comp

attribute [colib_tag "COL-0072",
  colib_ref "WeibelKBook" "IV, functoriality paragraph following Definition 6.3, page 54"
    "background" "Explicit normalized Q-functor and pi-map identification used for composition"]
  CategoryTheory.ExactCategory.ExactFunctor.normalizedQ_map_point
  CategoryTheory.ExactCategory.ExactFunctor.KMap_eq_piMap
