/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremA.ReplacementEntry
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/ConstantNerveReplacement.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.
 # The original entry into a constant nerve replacement over an initial base

The replacement is the nerve of the product category, degree by degree. The
entry is the actual inclusion at the initial object, hence a left adjoint.
No theorem about realization preserving arbitrary topological products is used.
-/
@[expose] public section
noncomputable section
open SSet TopCat Convexity.StdSimplex
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
namespace CategoryTheory.TheoremA
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D : Type u} [SmallCategory D] (A : Type u) [SmallCategory A]

/-- A pair of chains is the original chain in the product category. -/
def constantNerveReplacementIso :
    replacementDiagonal ((Functor.const D).obj (nerve A)) ≅ nerve (D × A) :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso
    { toFun := fun x ↦ x.1.prod' x.2
      invFun := fun σ ↦ ⟨σ ⋙ CategoryTheory.Prod.fst D A,
        σ ⋙ CategoryTheory.Prod.snd D A⟩
      left_inv := by intro x; cases x; rfl
      right_inv := by
        intro σ
        apply CategoryTheory.Functor.ext (fun _ ↦ rfl) }) (by
    intro p q α
    rfl)

/-- The original inclusion fixes the displayed indexing object. -/
def constantNerveEntryFunctor (i : D) : A ⥤ D × A :=
  ((Functor.const A).obj i).prod' (𝟭 A)

/-- The simplicial entry is exactly the nerve of the categorical inclusion. -/
theorem constantNerveReplacementIso_entry (i : D) :
    replacementEntry ((Functor.const D).obj (nerve A)) i ≫
      (constantNerveReplacementIso A).hom = nerveMap (constantNerveEntryFunctor A i) := by
  rfl

/-- Initiality supplies the genuine product-category counit. -/
def constantNerveEntryCounit (i : D) (hi : IsInitial i) :
    CategoryTheory.Prod.snd D A ⋙ constantNerveEntryFunctor A i ⟶ 𝟭 (D × A) where
  app X := (hi.to X.1, 𝟙 X.2)
  naturality X Y f := by
    apply Prod.ext
    · exact hi.hom_ext _ _
    · simp [constantNerveEntryFunctor]

/-- The original inclusion at an initial object is left adjoint to projection. -/
def constantNerveEntryAdjunction (i : D) (hi : IsInitial i) :
    constantNerveEntryFunctor A i ⊣ CategoryTheory.Prod.snd D A :=
  Adjunction.mkOfUnitCounit {
    unit := { app := fun X ↦ 𝟙 X }
    counit := constantNerveEntryCounit A i hi
    left_triangle := by
      apply NatTrans.ext
      funext X
      apply Prod.ext
      · exact hi.hom_ext _ _
      · simp [constantNerveEntryCounit, constantNerveEntryFunctor]
    right_triangle := by
      ext X
      simp [constantNerveEntryCounit, constantNerveEntryFunctor] }

/-- The constant replacement entry is a genuine homotopy equivalence with its
original simplicial entry as forward map. -/
def constantNerveReplacementEntryHomotopyEquiv (i : D) (hi : IsInitial i) :
    ContinuousMap.HomotopyEquiv |nerve A|
      |replacementDiagonal ((Functor.const D).obj (nerve A))| :=
  (adjunctionClassifyingHomotopyEquivUniversal (constantNerveEntryAdjunction A i hi)).trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (constantNerveReplacementIso A).symm)).toHomotopyEquiv

@[simp]
theorem constantNerveReplacementEntryHomotopyEquiv_toFun (i : D) (hi : IsInitial i) :
    (constantNerveReplacementEntryHomotopyEquiv A i hi).toFun =
      (SSet.toTop.map (replacementEntry ((Functor.const D).obj (nerve A)) i)).hom := by
  change (SSet.toTop.map (constantNerveReplacementIso A).inv).hom.comp
    (classifyingSpaceMapUniversal (constantNerveEntryFunctor A i)) = _
  rw [classifyingSpaceMapUniversal_eq]
  change (SSet.toTop.map (nerveMap (constantNerveEntryFunctor A i)) ≫
    SSet.toTop.map (constantNerveReplacementIso A).inv).hom = _
  rw [← Functor.map_comp, ← constantNerveReplacementIso_entry,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end CategoryTheory.TheoremA
