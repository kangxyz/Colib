/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Biproducts
public import Colib.CategoryTheory.ExactCategory.Isomorphisms
public import Colib.CategoryTheory.ExactCategory.Filtration.PullbackFlag
public import Colib.CategoryTheory.ComposableArrows.Append


/-! # Extending admissible flags by a zero and an ambient target -/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows ZeroObject
open CategoryTheory.ComposableArrows
universe u v

namespace CategoryTheory.ExactCategory.Filtration
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) {n : ℕ} (A : ComposableArrows C n)

/-- Admissibility of neighboring arrows suffices for a whole finite flag. -/
theorem flag_inflation_of_successors
    (hA : ∀ (i : ℕ) (hi : i < n), E.inflation (A.map' i (i + 1)))
    {i j : Fin (n + 1)} (f : i ⟶ j) : E.inflation (A.map f) := by
  suffices ∀ (k i j : ℕ) (hj : i + k = j) (hj' : j ≤ n),
      E.inflation (A.map' i j) by
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    have hij : i ≤ j := leOfHom f
    obtain ⟨k, hk⟩ := Nat.le.dest hij
    exact this k i j hk (by omega)
  intro k
  induction k with
  | zero =>
    intro i j hj hj'
    simp only [Nat.add_zero] at hj
    subst j
    rw [A.map'_self i hj']
    exact E.inflation_id _
  | succ k ih =>
    intro i j hj hj'
    rw [← Nat.add_assoc] at hj
    subst j
    rw [A.map'_comp i (i + k) (i + k + 1)]
    exact E.inflation_comp _ _ (ih i (i + k) rfl (by omega)) (hA (i + k) (by omega))

/-- Prefix an actual zero object to a flag. -/
def zeroPrefixFlag : ComposableArrows C (n + 1) :=
  A.precomp (0 : (0 : C) ⟶ A.obj 0)

@[simp]
theorem zeroPrefixFlag_obj_zero : (zeroPrefixFlag A).obj 0 = (0 : C) := rfl

@[simp]
theorem zeroPrefixFlag_obj_succ (i : Fin (n + 1)) :
    (zeroPrefixFlag A).obj i.succ = A.obj i := rfl

@[simp]
theorem zeroPrefixFlag_map_succ {i j : Fin (n + 1)} (f : i ⟶ j) :
    (zeroPrefixFlag A).map ((Fin.succFunctor (n + 1)).map f) = A.map f := rfl

/-- Prefixing zero preserves admissibility without a condition on the old first term. -/
theorem zeroPrefixFlag_inflation
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
    {i j : Fin (n + 1 + 1)} (f : i ⟶ j) :
    E.inflation ((zeroPrefixFlag A).map f) := by
  apply flag_inflation_of_successors E
  intro i hi
  cases i with
  | zero => exact E.inflation_zero _
  | succ i => exact hA _

variable {Y : C} (q : A.obj (Fin.last n) ⟶ Y)

/-- Appending an inflation to an admissible flag is admissible. -/
theorem appendFlag_inflation
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f)) (hq : E.inflation q)
    {i j : Fin (n + 1 + 1)} (f : i ⟶ j) :
    E.inflation ((appendChain A q).map f) := by
  apply flag_inflation_of_successors E
  intro i hi
  change E.inflation ((ComposableArrows.mkOfObjOfMapSucc _ _).map' i (i + 1))
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  suffices ∀ (i : Fin (n + 1)), E.inflation (appendChainSucc A q i) from this ⟨i, hi⟩
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [appendChainSucc, Fin.lastCases_last]
    exact E.inflation_comp _ _
      (E.inflation_of_iso (eqToIso (appendChainObj_castSucc A (Fin.last n))))
      (E.inflation_comp _ _ hq
        (E.inflation_of_iso (eqToIso (appendChainObj_last A).symm)))
  | cast i =>
    simp only [appendChainSucc, Fin.lastCases_castSucc]
    exact E.inflation_comp _ _
      (E.inflation_of_iso (eqToIso (appendChainObj_castSucc A i.castSucc)))
      (E.inflation_comp _ _ (hA _)
        (E.inflation_of_iso (eqToIso (appendChainObj_succ_castSucc A i).symm)))

section PullbackExtension
variable {P : C} (p : P ⟶ A.obj (Fin.last n)) (hp : E.deflation p)
  {Z : C} (r : P ⟶ Z)

/-- Pull back the old flag, prefix a genuine zero, and append the new target.
All required pullbacks are supplied by the exact-category axioms. -/
def extendedPullbackFlag : ComposableArrows C (n + 1 + 1) := by
  letI (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  exact zeroPrefixFlag (appendChain (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r))

/-- The extended flag is admissible from ordinary inflation/deflation data. -/
theorem extendedPullbackFlag_inflation
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f)) (hr : E.inflation r)
    {i j : Fin (n + 1 + 1 + 1)} (f : i ⟶ j) :
    E.inflation ((extendedPullbackFlag E A p hp r).map f) := by
  let (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  exact zeroPrefixFlag_inflation E _
    (appendFlag_inflation E _ _ (pullbackFlag_inflation E A p hp hA)
      (E.inflation_comp _ _ (E.inflation_of_iso (pullbackFlagTopIso A p)) hr)) f

@[simp]
theorem extendedPullbackFlag_obj_zero :
    (extendedPullbackFlag E A p hp r).obj 0 = (0 : C) := rfl

@[simp]
theorem extendedPullbackFlag_obj_last :
    (extendedPullbackFlag E A p hp r).obj (Fin.last (n + 1 + 1)) = Z := by
  let (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  exact appendChain_obj_last (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r)

variable [∀ i : Fin (n + 1), HasPullback p (flagTopMap A i)]

@[simp]
theorem extendedPullbackFlag_obj_middle (i : Fin (n + 1)) :
    (extendedPullbackFlag E A p hp r).obj i.castSucc.succ = (pullbackFlag A p).obj i :=
  appendChain_obj_castSucc (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r) i

/-- The actual middle terms and arrows of the extension recover the pullback flag. -/
def extendedPullbackFlagMiddleIso :
    (Fin.castSuccFunctor (n + 1) ⋙ Fin.succFunctor (n + 1 + 1)) ⋙
      extendedPullbackFlag E A p hp r ≅ pullbackFlag A p :=
  appendChainRestrictionIso (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r)

/-- The actual inclusion of every middle term into the final target is its
pullback projection followed by the prescribed inflation. -/
theorem extendedPullbackFlag_middle_to_last (i : Fin (n + 1)) :
    (extendedPullbackFlag E A p hp r).map (homOfLE (Fin.le_last i.castSucc.succ)) ≫
        eqToHom (extendedPullbackFlag_obj_last E A p hp r) =
      eqToHom (extendedPullbackFlag_obj_middle E A p hp r i) ≫
        pullback.fst p (flagTopMap A i) ≫ r := by
  change (appendChain (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r)).map
    (homOfLE (Fin.le_last i.castSucc)) ≫ _ = _
  rw [appendChain_to_last]
  simp only [pullbackFlagTopIso_hom]
  exact congrArg (fun t ↦ eqToHom (extendedPullbackFlag_obj_middle E A p hp r i) ≫ t)
    (pullbackFlag_map_fst_assoc A p (homOfLE (Fin.le_last i)) r)

end PullbackExtension

end CategoryTheory.ExactCategory.Filtration
