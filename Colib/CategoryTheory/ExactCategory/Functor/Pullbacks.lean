/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.MatrixDeflation
public import Mathlib.Algebra.Homology.CommSq

/-!
# Exact functors preserve admissible pullbacks

An additive functor preserving the selected conflations preserves pullback squares
along admissible epimorphisms. No abelian structure or arbitrary pullbacks are required.
The conclusion concerns the actual images of all four maps of the supplied square.

## Implementation provenance

Extracted from `Aglib/CategoryTheory/ExactCategory/Functor.lean` at
`2c34f185fa859e862661f939cd216b07bcccfb26`. The source's signed matrix is retained:
its row is `[-i, p]` and its kernel column is `[a, b]`. The kernel calculation is
adapted to Mathlib's universal property for the opposite signed row `[i, -p]`.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.ExactCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]

namespace ExactStructure

/-- A chosen kernel of an admissible epimorphism is its specified conflation. -/
lemma conflation_of_isKernel (E : ExactStructure C) {X Y Z : C}
    {i : X ⟶ Y} {p : Y ⟶ Z} (h : i ≫ p = 0)
    (hi : IsLimit (KernelFork.ofι i h)) (hp : E.deflation p) :
    E.conflation (ShortComplex.mk i p h) := by
  obtain ⟨X', i', h', hs⟩ := hp
  let hi' := E.kernel (ShortComplex.mk i' p h') hs
  let e : X' ≅ X := hi'.conePointUniqueUpToIso hi
  have he : e.hom ≫ i = i' :=
    hi'.conePointUniqueUpToIso_hom_comp hi WalkingParallelPair.zero
  let se : ShortComplex.mk i' p h' ≅ ShortComplex.mk i p h :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by simpa using he) (by simp)
  exact E.iso_closed se hs

end ExactStructure

/-- The total kernel of a pullback square in an additive category. No abelian
hypothesis or ambient existence of arbitrary pullbacks is needed. -/
def pullbackMatrixKernel {P A B T : C} {a : P ⟶ A} {b : P ⟶ B}
    {i : A ⟶ T} {p : B ⟶ T} (sq : IsPullback a b i p) :
    IsLimit (KernelFork.ofι (biprod.lift a b)
      (show biprod.lift a b ≫ biprod.desc (-i) p = 0 by
        simp only [biprod.lift_desc, comp_neg, sq.w, neg_add_cancel])) := by
  let h := sq.isLimitKernelFork
  have flipZero {W : C} (g : W ⟶ A ⊞ B)
      (hg : g ≫ biprod.desc (-i) p = 0) : g ≫ biprod.desc i (-p) = 0 := by
    simpa [biprod.desc_eq, Preadditive.comp_add, comp_neg, neg_comp, neg_add, add_comm] using
      congrArg Neg.neg hg
  refine KernelFork.IsLimit.ofι _ _
    (fun g hg => h.lift (KernelFork.ofι g (flipZero g hg))) ?_ ?_
  · intro W g hg
    exact h.fac (KernelFork.ofι g (flipZero g hg)) WalkingParallelPair.zero
  · intro W g hg m hm
    apply Fork.IsLimit.hom_ext h
    exact hm.trans (h.fac (KernelFork.ofι g (flipZero g hg))
      WalkingParallelPair.zero).symm

namespace ExactFunctor

variable {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

/-- Exact additive functors preserve pullback squares along admissible epimorphisms.
The proof applies exactness to the total kernel–cokernel pair of the square. -/
theorem map_isPullback {P A B T : C} {a : P ⟶ A} {b : P ⟶ B}
    {i : A ⟶ T} {p : B ⟶ T} (sq : IsPullback a b i p) (hp : E.deflation p) :
    IsPullback (F.toFunctor.map a) (F.toFunctor.map b)
      (F.toFunctor.map i) (F.toFunctor.map p) := by
  let S : ShortComplex C := ShortComplex.mk (biprod.lift a b) (biprod.desc (-i) p)
    (by simp only [biprod.lift_desc, comp_neg, sq.w, neg_add_cancel])
  have hs : E.conflation S := E.conflation_of_isKernel _ (pullbackMatrixKernel sq)
    (E.deflation_biprod_desc (-i) p hp)
  let hF := E'.kernel (S.map F.toFunctor) (F.map_conflation S hs)
  let pair (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      s.pt ⟶ F.toFunctor.obj (A ⊞ B) :=
    s.fst ≫ F.toFunctor.map biprod.inl + s.snd ≫ F.toFunctor.map biprod.inr
  have pair_zero (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      pair s ≫ F.toFunctor.map (biprod.desc (-i) p) = 0 := by
    dsimp only [pair]
    simp only [add_comp, Category.assoc, ← F.toFunctor.map_comp,
      biprod.inl_desc, biprod.inr_desc, F.toFunctor.map_neg, comp_neg,
      s.condition, neg_add_cancel]
  let cone (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :=
    KernelFork.ofι (pair s) (pair_zero s)
  have lift_fac (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      hF.lift (cone s) ≫ F.toFunctor.map (biprod.lift a b) = pair s :=
    hF.fac (cone s) WalkingParallelPair.zero
  have pair_fst (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      pair s ≫ F.toFunctor.map biprod.fst = s.fst := by
    simp [pair, ← F.toFunctor.map_comp]
  have pair_snd (s : PullbackCone (F.toFunctor.map i) (F.toFunctor.map p)) :
      pair s ≫ F.toFunctor.map biprod.snd = s.snd := by
    simp [pair, ← F.toFunctor.map_comp]
  have w : F.toFunctor.map a ≫ F.toFunctor.map i =
      F.toFunctor.map b ≫ F.toFunctor.map p := by
    simp only [← F.toFunctor.map_comp, sq.w]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s => hF.lift (cone s)) ?_ ?_ ?_)
  · intro s
    have h := congrArg (fun k => k ≫ F.toFunctor.map biprod.fst) (lift_fac s)
    simpa only [Category.assoc, ← F.toFunctor.map_comp, biprod.lift_fst, pair_fst] using h
  · intro s
    have h := congrArg (fun k => k ≫ F.toFunctor.map biprod.snd) (lift_fac s)
    simpa only [Category.assoc, ← F.toFunctor.map_comp, biprod.lift_snd, pair_snd] using h
  · intro s m hm₁ hm₂
    let : Mono (F.toFunctor.map (biprod.lift a b)) := Fork.IsLimit.mono hF
    apply (cancel_mono (F.toFunctor.map (biprod.lift a b))).1
    rw [lift_fac]
    simp only [biprod.lift_eq, F.toFunctor.map_add, F.toFunctor.map_comp,
      comp_add, ← Category.assoc, hm₁, hm₂, pair]

/-- Preservation of pullbacks along admissible epimorphisms, expressed in
mathlib's standard limit-preservation language. -/
theorem preserves_pullback {A B T : C} (i : A ⟶ T) (p : B ⟶ T)
    (hp : E.deflation p) : PreservesLimit (cospan i p) F.toFunctor := by
  let : HasPullback p i := E.deflation.hasPullback i hp
  let : HasPullback i p := hasPullback_symmetry p i
  let sq := F.map_isPullback (IsPullback.of_hasPullback i p) hp
  apply preservesLimit_of_preserves_limit_cone (pullbackIsPullback i p)
  exact (PullbackCone.isLimitMapConeEquiv _ F.toFunctor).symm sq.isLimit

end ExactFunctor
end CategoryTheory.ExactCategory

attribute [colib_tag "COL-0033",
  colib_ref "BuhlerExactCategories" "Proposition 5.2, pullback clause" "clause"
    "Exact additive functors preserve pullbacks along admissible epimorphisms"]
  CategoryTheory.ExactCategory.ExactFunctor.map_isPullback
  CategoryTheory.ExactCategory.ExactFunctor.preserves_pullback
