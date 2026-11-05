/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.CanonicalMap
public import Colib.Topology.Realization.Constant
public import Colib.Topology.Homotopy.HomotopyGroup.Constant

/-!
# The actual zero functor and its trivial K-map

Adapted from Quillen/Waldhausen/Functoriality/KMap.lean:181–214 at commit
c561118b7795eb9780be9ed391c3251d6a4d0afd. This preserves the actual constant
chosen-zero functor, simplicial map, realization map and homotopy-group map.
The S-model remains unnormalized with IsZero diagonal. No additivity theorem,
strict S-model comparison or K0 commutativity is asserted.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The actual constant functor at the specified target zero. -/
def zeroFunctor (W : Structure D) : C ⥤ D :=
  (Functor.const C).obj W.zero

/-- The actual chosen-zero functor is exact for every Waldhausen structure. -/
theorem zeroFunctor_isExact (V : Structure C) (W : Structure D) :
    IsExact V.cof V.weq W.cof W.weq (zeroFunctor (C := C) W) where
  zero _ := W.isZero
  cofibration _ _ := W.cof.id_mem W.zero
  weak _ _ := W.weq.id_mem W.zero
  pushout _ _ := IsPushout.id_horiz (𝟙 W.zero)

/-- Its original simplicial map is exactly the constant chosen-zero map. -/
theorem sSetMap_zeroFunctor (V : Structure C) (W : Structure D) :
    sSetMap (zeroFunctor_isExact V W) =
      SSet.const (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
  ext n A
  apply Subtype.ext
  rfl

/-- Its original realization map is exactly the constant chosen-zero map. -/
theorem deloopingMap_zeroFunctor (V : Structure C) (W : Structure D) :
    (deloopingMap (zeroFunctor_isExact V W)).hom =
      ContinuousMap.const V.Delooping W.kBasepoint := by
  ext p
  change SSet.toTop.map (sSetMap (zeroFunctor_isExact V W)) p = W.kBasepoint
  rw [sSetMap_zeroFunctor]
  exact SSet.realization_const_apply _ p

/-- The actual zero functor gives the trivial original K-homomorphism. -/
@[simp] theorem KMap_zeroFunctor (V : Structure C) (W : Structure D) (n : ℕ) :
    KMap (zeroFunctor_isExact V W) n = 1 := by
  rw [KMap_eq_piMap_of_zeroEq (zeroFunctor_isExact V W) rfl n]
  simp only [deloopingMap_zeroFunctor]
  exact HomotopyGroup.piMap_const n

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0158",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "The actual zero-functor unit degeneration, not additivity or a strict-model comparison"]
  CategoryTheory.Waldhausen.zeroFunctor_isExact
  CategoryTheory.Waldhausen.KMap_zeroFunctor
