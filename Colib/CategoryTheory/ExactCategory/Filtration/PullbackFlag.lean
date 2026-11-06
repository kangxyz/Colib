/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic



/-!
# Pulling an admissible flag back along a deflation

All flag terms are actual pullbacks, their maps are actual admissible
monomorphisms, and the projection to the old flag is objectwise an
admissible epimorphism. The top term is canonically the original apex.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v

namespace CategoryTheory.ExactCategory.Filtration
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) {n : ℕ} (A : Fin (n + 1) ⥤ C)

/-- The actual inclusion of one flag term into its top term. -/
def flagTopMap (i : Fin (n + 1)) : A.obj i ⟶ A.obj (Fin.last n) :=
  A.map (homOfLE (Fin.le_last i))

omit [Preadditive C] [HasFiniteBiproducts C] in
@[reassoc (attr := simp)]
theorem flagTopMap_comp {i j : Fin (n + 1)} (f : i ⟶ j) :
    A.map f ≫ flagTopMap A j = flagTopMap A i := by
  simp only [flagTopMap, ← A.map_comp]
  congr 1

variable {P : C} (p : P ⟶ A.obj (Fin.last n)) (hp : E.deflation p)

include E hp in
theorem flagPullback_exists (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
  E.deflation.hasPullback _ hp

variable [hpb : ∀ i : Fin (n + 1), HasPullback p (flagTopMap A i)]

/-- Pull back each initial subobject along the new deflation. -/
def pullbackFlag : Fin (n + 1) ⥤ C where
  obj i := pullback p (flagTopMap A i)
  map {i j} f := pullback.lift (pullback.fst p (flagTopMap A i))
    (pullback.snd p (flagTopMap A i) ≫ A.map f) (by
      rw [Category.assoc, flagTopMap_comp, pullback.condition])
  map_id i := by
    apply pullback.hom_ext <;> simp
  map_comp f g := by
    apply pullback.hom_ext <;> simp [Category.assoc]

omit [Preadditive C] [HasFiniteBiproducts C] in
@[reassoc (attr := simp)]
theorem pullbackFlag_map_fst {i j : Fin (n + 1)} (f : i ⟶ j) :
    (pullbackFlag A p).map f ≫ pullback.fst p (flagTopMap A j) =
      pullback.fst p (flagTopMap A i) := by simp [pullbackFlag]

omit [Preadditive C] [HasFiniteBiproducts C] in
@[reassoc (attr := simp)]
theorem pullbackFlag_map_snd {i j : Fin (n + 1)} (f : i ⟶ j) :
    (pullbackFlag A p).map f ≫ pullback.snd p (flagTopMap A j) =
      pullback.snd p (flagTopMap A i) ≫ A.map f := by simp [pullbackFlag]

/-- The pulled-back flag maps naturally to the original flag. -/
def pullbackFlagToOriginal : pullbackFlag A p ⟶ A where
  app i := pullback.snd p (flagTopMap A i)
  naturality {_ _} f := pullbackFlag_map_snd A p f

include hp in
/-- Every component of the projection is an actual admissible epimorphism. -/
theorem pullbackFlagToOriginal_deflation (i : Fin (n + 1)) :
    E.deflation ((pullbackFlagToOriginal A p).app i) :=
  E.deflation.pullback_snd p (flagTopMap A i) hp

/-- The maps to the new apex form an actual cocone. -/
def pullbackFlagToApex : pullbackFlag A p ⟶ (Functor.const _).obj P where
  app i := pullback.fst p (flagTopMap A i)
  naturality f := by simp

omit [Preadditive C] [HasFiniteBiproducts C] in
/-- Every map of pulled-back flag terms is a genuine pullback of the
corresponding original map, against a deflation. -/
theorem pullbackFlag_map_isPullback {i j : Fin (n + 1)} (f : i ⟶ j) :
    IsPullback ((pullbackFlag A p).map f)
      (pullback.snd p (flagTopMap A i)) (pullback.snd p (flagTopMap A j)) (A.map f) := by
  have hs : IsPullback
      ((pullbackFlag A p).map f ≫ pullback.fst p (flagTopMap A j))
      (pullback.snd p (flagTopMap A i)) p (A.map f ≫ flagTopMap A j) := by
    simpa only [pullbackFlag_map_fst, flagTopMap_comp] using
      IsPullback.of_hasPullback p (flagTopMap A i)
  exact hs.of_right (pullbackFlag_map_snd A p f)
    (IsPullback.of_hasPullback p (flagTopMap A j))

include hp in
/-- Pullback along a deflation preserves admissibility of every flag map. -/
theorem pullbackFlag_inflation
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    E.inflation ((pullbackFlag A p).map f) :=
  E.inflation_of_isPullback (pullbackFlag_map_isPullback A p f).flip (hA f)
    (pullbackFlagToOriginal_deflation E A p hp j)

include hp in
/-- Each pulled-back term is an actual admissible subobject of the apex. -/
theorem pullbackFlagToApex_inflation
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f)) (i : Fin (n + 1)) :
    E.inflation ((pullbackFlagToApex A p).app i) :=
  E.inflation_of_isPullback (IsPullback.of_hasPullback p (flagTopMap A i)).flip
    (hA (homOfLE (Fin.le_last i))) hp

/-- The top pullback is the original apex, with its actual first projection. -/
def pullbackFlagTopIso : (pullbackFlag A p).obj (Fin.last n) ≅ P := by
  haveI : IsIso (flagTopMap A (Fin.last n)) := by
    change IsIso (A.map (𝟙 (Fin.last n)))
    rw [A.map_id]
    infer_instance
  haveI : IsIso (pullback.fst p (flagTopMap A (Fin.last n))) :=
    (IsPullback.of_hasPullback p (flagTopMap A (Fin.last n))).isIso_fst_of_isIso
  exact asIso (pullback.fst p (flagTopMap A (Fin.last n)))

omit [Preadditive C] [HasFiniteBiproducts C] in
@[simp]
theorem pullbackFlagTopIso_hom :
    (pullbackFlagTopIso A p).hom = pullback.fst p (flagTopMap A (Fin.last n)) := rfl

/-- When the old flag starts at zero, its first pullback is the genuine
kernel of the new deflation. -/
def pullbackFlagInitialKernel (hzero : IsZero (A.obj 0)) :
    IsLimit (KernelFork.ofι (pullback.fst p (flagTopMap A 0))
      (show pullback.fst p (flagTopMap A 0) ≫ p = 0 from by
        rw [pullback.condition]
        exact (congrArg (fun f ↦ pullback.snd p (flagTopMap A 0) ≫ f)
          (hzero.eq_of_src (flagTopMap A 0) 0)).trans (comp_zero))) := by
  refine KernelFork.IsLimit.ofι _ _
    (fun {W} a ha ↦ pullback.lift a 0 (by simpa using ha)) ?_ ?_
  · intro W a ha
    simp
  · intro W a ha m hm
    apply pullback.hom_ext
    · simpa using hm
    · exact hzero.eq_of_tgt _ _

end CategoryTheory.ExactCategory.Filtration
