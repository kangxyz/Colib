/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.Transpose
public import Colib.AlgebraicTopology.SimplicialSet.Diagonal
public import Colib.CategoryTheory.TheoremA.ReplacementDiagonal

/-! # Exact mixed-nerve transpose isomorphisms

The explicit index switch commutes with both original ordinal restrictions
and with the literal inclusion of coarse-weak cofibration arrows. No nerve
comparison equivalence is assumed: these are isomorphisms of presentations
of the same original double diagrams.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/TransposeNerves.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration.RelativeRows


noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
open RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The actual coarse/fine nerve is the transpose of the original horizontal nerve. -/
def coarseTransposeIso : (coarseChainNerve N).flip ≅ horizontalNerve N :=
  NatIso.ofComponents (fun k ↦ NatIso.ofComponents
    (fun n ↦ Equiv.toIso (transposeCoarseEquiv N n.unop k.unop)) (by
      intro n m α
      ext F : 3
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl))) (by
    intro k l β
    ext n F : 4
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl))

/-- The same actual index switch retains the original cofibration predicates. -/
def cofTransposeIso : (cofChainNerve N).flip ≅ horizontalCofNerve N :=
  NatIso.ofComponents (fun k ↦ NatIso.ofComponents
    (fun n ↦ Equiv.toIso (transposeCofEquiv N n.unop k.unop)) (by
      intro n m α
      ext F : 3
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl))) (by
    intro k l β
    ext n F : 4
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl))

/-- The underlying function uses the unflipped, canonical nerve object types. -/
@[simp] theorem coarseTransposeIso_hom_app_hom (n k : SimplexCategory) :
    TypeCat.Hom.hom (X := ((coarseChainNerve N).obj (op n)).obj (op k))
      (Y := ((horizontalNerve N).obj (op k)).obj (op n)) (((coarseTransposeIso N).hom.app (op
          k)).app (op n)) =
      TypeCat.Fun.mk (transposeCoarse N n k) := rfl


/-- The underlying function uses the unflipped, canonical nerve object types. -/
@[simp] theorem coarseTransposeIso_inv_app_hom (n k : SimplexCategory) :
    TypeCat.Hom.hom (X := ((horizontalNerve N).obj (op k)).obj (op n))
      (Y := ((coarseChainNerve N).obj (op n)).obj (op k)) (((coarseTransposeIso N).inv.app (op
          k)).app (op n)) =
      TypeCat.Fun.mk (untransposeCoarse N n k) := rfl


/-- The underlying function uses the unflipped, canonical nerve object types. -/
@[simp] theorem cofTransposeIso_hom_app_hom (n k : SimplexCategory) :
    TypeCat.Hom.hom (X := ((cofChainNerve N).obj (op n)).obj (op k))
      (Y := ((horizontalCofNerve N).obj (op k)).obj (op n)) (((cofTransposeIso N).hom.app (op
          k)).app (op n)) =
      TypeCat.Fun.mk (transposeCof N n k) := rfl


/-- The underlying function uses the unflipped, canonical nerve object types. -/
@[simp] theorem cofTransposeIso_inv_app_hom (n k : SimplexCategory) :
    TypeCat.Hom.hom (X := ((horizontalCofNerve N).obj (op k)).obj (op n))
      (Y := ((cofChainNerve N).obj (op n)).obj (op k)) (((cofTransposeIso N).inv.app (op k)).app
          (op n)) =
      TypeCat.Fun.mk (untransposeCof N n k) := rfl


/-- Transposition intertwines the two actual inclusion maps strictly. -/
theorem transpose_inclusion :
    ((CategoryTheory.flipFunctor _ _ _).map (chainInclusion N)) ≫ (coarseTransposeIso N).hom =
      (cofTransposeIso N).hom ≫ horizontalNerveInclusion N := by
  ext k n F : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Original diagonal mixed diagrams are identified by the actual index switch. -/
def coarseDiagonalIso : SSet.diagonalSSet (coarseChainNerve N) ≅
    SSet.diagonalSSet (horizontalNerve N) :=
  (SSet.diagonalFlipIso (coarseChainNerve N)).symm ≪≫
    SSet.diagonalFunctor.mapIso (coarseTransposeIso N)

/-- The original diagonal cofibration diagrams have the same literal presentation change. -/
def cofDiagonalIso : SSet.diagonalSSet (cofChainNerve N) ≅
    SSet.diagonalSSet (horizontalCofNerve N) :=
  (SSet.diagonalFlipIso (cofChainNerve N)).symm ≪≫
    SSet.diagonalFunctor.mapIso (cofTransposeIso N)

@[simp] theorem coarseDiagonalIso_hom_app (n : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N n) n.len) :
    (coarseDiagonalIso N).hom.app (op n) F = transposeCoarse N n n F := rfl

@[simp] theorem cofDiagonalIso_hom_app (n : SimplexCategory)
    (F : ComposableArrows (FineWeakChains N n) n.len) :
    (cofDiagonalIso N).hom.app (op n) F = transposeCof N n n F := rfl

/-- The diagonal presentation square uses the literal original inclusion on both sides. -/
theorem diagonal_inclusion :
    SSet.diagonalMap (chainInclusion N) ≫ (coarseDiagonalIso N).hom =
      (cofDiagonalIso N).hom ≫ SSet.diagonalMap (horizontalNerveInclusion N) := by
  ext n F : 4
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.MixedNerves
