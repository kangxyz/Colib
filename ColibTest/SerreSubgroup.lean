/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.GrothendieckGroup.SerreSubgroup

@[expose] public noncomputable section

universe v u

namespace ColibTest.SerreSubgroup

open CategoryTheory CategoryTheory.ExactCategory

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.IsSerreClass]

attribute [local instance] Abelian.hasFiniteBiproducts

example : (serreSubgroup P).map (abelianGrothendieckEquiv A).toAddMonoidHom =
    (GrothendieckGroup.map P.ι P.shortExact_map_ι).range :=
  map_serreSubgroup_eq_range_of_isSerreClass P

example (X : P.FullSubcategory) :
    GrothendieckGroup.map P.ι P.shortExact_map_ι (GrothendieckGroup.of X) =
      abelianGrothendieckEquiv A ((abelianExactStructure A).grothendieckClass X.obj) :=
  map_ι_of_eq_abelianGrothendieckEquiv_class P P.shortExact_map_ι X

example {X : A} (hX : P X) :
    abelianGrothendieckEquiv A ((abelianExactStructure A).grothendieckClass X) ∈
      (GrothendieckGroup.map P.ι P.shortExact_map_ι).range := by
  rw [abelianGrothendieckEquiv_class]
  exact GrothendieckGroup.of_mem_range_map_ι P P.shortExact_map_ι hX

example {X : A} (hX : P X) :
    (abelianExactStructure A).grothendieckClass X ∈ serreSubgroup P :=
  AddSubgroup.subset_closure ⟨X, hX, rfl⟩

example {X Y : A} (hX : P X) (hY : P Y) :
    (abelianExactStructure A).grothendieckClass X -
      (abelianExactStructure A).grothendieckClass Y ∈ serreSubgroup P :=
  (serreSubgroup P).sub_mem
    (AddSubgroup.subset_closure ⟨X, hX, rfl⟩)
    (AddSubgroup.subset_closure ⟨Y, hY, rfl⟩)

example (hι : ∀ ⦃S : ShortComplex P.FullSubcategory⦄,
    S.ShortExact → (S.map P.ι).ShortExact) :
    (GrothendieckGroup.map P.ι hι).range =
      AddSubgroup.closure {a | ∃ X : A, P X ∧ a = GrothendieckGroup.of X} :=
  GrothendieckGroup.range_map_ι_eq_closure P hι

end ColibTest.SerreSubgroup
