/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Quillen.Map.Functoriality

/-!
# Based homotopy invariance and actual Quillen K-map composition

Topological source, target and loop-index universes are independent. The exact
functors retain the shared object and morphism universes of the composition law.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped Topology unitInterval ZeroObject

universe w v u

noncomputable section

section Topology

variable {N : Type w} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
  {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
  (H : f.Homotopy g) (hH : ∀ t, H (t, x) = y)

example (p : GenLoop N X x) :
    (GenLoop.postcomp f hf p).val.HomotopyRel (GenLoop.postcomp g hg p).val
      (Cube.boundary N) := GenLoop.postcompHomotopy hf hg H hH p

example (p : GenLoop N X x) (t : unitInterval) (z : N → unitInterval) :
    GenLoop.postcompHomotopy hf hg H hH p (t, z) = H (t, p z) := rfl

example : HomotopyGroup.map (N := N) f hf = HomotopyGroup.map g hg :=
  HomotopyGroup.map_eq_of_based_homotopy hf hg H hH

example [DecidableEq N] [Nonempty N] :
    HomotopyGroup.mapHom (N := N) f hf = HomotopyGroup.mapHom g hg :=
  HomotopyGroup.mapHom_eq_of_based_homotopy hf hg H hH

example (n : ℕ) : HomotopyGroup.piMap n f hf = HomotopyGroup.piMap n g hg :=
  HomotopyGroup.piMap_eq_of_based_homotopy n hf hg H hH

example (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.piMap n f hf a = HomotopyGroup.piMap n g hg a :=
  DFunLike.congr_fun (HomotopyGroup.piMap_eq_of_based_homotopy n hf hg H hH) a

example (n : ℕ) (R : f.HomotopyRel g {x}) :
    HomotopyGroup.piMap n f hf = HomotopyGroup.piMap n g hg := by
  apply HomotopyGroup.piMap_eq_of_based_homotopy n hf hg R.toHomotopy
  intro t
  exact (R.prop t x (Set.mem_singleton x)).trans hf

end Topology

section Exact

variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  [Preadditive T] [HasFiniteBiproducts T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}
  (F : ExactFunctor EC ED) (G : ExactFunctor ED ET)

example : classifyingSpaceMap F.normalizedQ EC.kBasepoint = ED.kBasepoint :=
  F.normalizedQ_map_point

example (n : ℕ) : F.KMap n = HomotopyGroup.piMap n
    (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point := rfl

example (n : ℕ) : (ExactFunctor.id EC).KMap n = MonoidHom.id (EC.K n) :=
  ExactFunctor.KMap_id EC n

example (n : ℕ) : (F.comp G).KMap n = (G.KMap n).comp (F.KMap n) :=
  F.KMap_comp G n

example (n : ℕ) (a : EC.K n) : (F.comp G).KMap n a = G.KMap n (F.KMap n a) :=
  DFunLike.congr_fun (F.KMap_comp G n) a

end Exact
