/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

import Colib.CategoryTheory.Waldhausen.Product.SSet
import Colib.CategoryTheory.Waldhausen.Additivity.CoproductFunctor
import Colib.Topology.Homotopy.HomotopyGroup.CompactLifting
import Colib.Topology.Homotopy.HomotopyGroup.Product

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen
open scoped Simplicial
universe u v u' v'

example {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    (V : Structure C) (W : Structure D) : Structure (C × D) := Product.productStructure V W

example {C D : Type u} [Category.{v} C] [Category.{v} D]
    (V : Structure C) (W : Structure D) :
    (Product.sSetIso V W).hom = Product.comparison V W := rfl

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (x : X) (y : Y) :
    Function.Bijective (Topology.piProdMap 0 x y) := Topology.piProdMap_bijective 0 x y

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : C(X, Y))
    (he : Function.Injective e) (hl : Topology.HasCompactSourceLifts e)
    {x : X} {y : Y} (h : e x = y) : Function.Bijective (HomotopyGroup.piMap 0 e h) :=
  Topology.piMap_bijective_of_compact_lifts e he hl h 0
