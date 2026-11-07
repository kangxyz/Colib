import Colib.KTheory.Waldhausen.Iterated.PrespectrumCompositionHomotopy

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory MonoidalCategory SSet Topology
open scoped Simplicial Topology unitInterval

universe u v

namespace WaldhausenIteratedCompositionTests

variable {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
  (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
  (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))

-- Actual simplicial maps, rather than pointwise homotopy classes.
example (r : ℕ) : (stages r).obj V ⊗ Δ[2] ⟶ (stages r).obj W :=
  stageTransformationTriangle r η θ hη hθ

example (r : ℕ) :
    (𝟙 ((stages r).obj V) ⊗ₘ SSet.stdSimplex.δ 2) ≫
      stageTransformationTriangle r η θ hη hθ = stageTransformationCylinder r η hη :=
  stageTransformationTriangle_first η θ hη hθ r

example (r : ℕ) :
    (𝟙 ((stages r).obj V) ⊗ₘ SSet.stdSimplex.δ 0) ≫
      stageTransformationTriangle r η θ hη hθ = stageTransformationCylinder r θ hθ :=
  stageTransformationTriangle_second η θ hη hθ r

example (r : ℕ) :
    (𝟙 ((stages r).obj V) ⊗ₘ SSet.stdSimplex.δ 1) ≫
      stageTransformationTriangle r η θ hη hθ =
        stageTransformationCylinder r (η ≫ θ)
          (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) :=
  stageTransformationTriangle_composite η θ hη hθ r

example (r : ℕ) (n : SimplexCategoryᵒᵖ) (zeta : (Δ[2]).obj n) :
    stageTriangleFunction r η θ hη hθ n (stageZeroSimplex r V n) zeta =
      stageZeroSimplex r W n := stageTriangleFunction_zeroSimplex η θ hη hθ r n zeta

example (r : ℕ) :
    SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[2] ≫
        stageTransformationTriangle r η θ hη hθ =
      CartesianMonoidalCategory.fst Δ[0] Δ[2] ≫
        SSet.yonedaEquiv.symm (stageVertex r W) :=
  stageTransformationTriangle_fixed_vertex η θ hη hθ r

-- The simplex parameter and original suspension parameter remain independent.
example (r : ℕ) (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n)
    (τ : (Δ[1]).obj n) (zeta : (Δ[2]).obj n) :
    stageTriangleFunction (r + 1) η θ hη hθ n ((stageCylinder r V).app n (A, τ)) zeta =
      (stageCylinder r W).app n (stageTriangleFunction r η θ hη hθ n A zeta, τ) :=
  stageTriangleFunction_structure r η θ hη hθ n A τ zeta

example (r : ℕ) :
    stageCylinder r V ▷ Δ[2] ≫ stageTransformationTriangle (r + 1) η θ hη hθ =
      simplicialSimplexCylinderSwap ((stages r).obj V) 2 ≫
        stageTransformationTriangle r η θ hη hθ ▷ Δ[1] ≫ stageCylinder r W :=
  stageTransformationTriangle_structure η θ hη hθ r

example (r : ℕ) : C(stageSpace r V × |(Δ[2] : SSet.{u})|, stageSpace r W) :=
  stageTriangleRealization η θ hη hθ r

example (r : ℕ) : Continuous (stageTriangleRealization η θ hη hθ r) :=
  (stageTriangleRealization η θ hη hθ r).continuous

example (r : ℕ) (z : |(Δ[2] : SSet.{u})|) (q : unitInterval) (x : stageSpace r V) :
    stageTriangleRealization η θ hη hθ (r + 1) (stageLoopMap r V x q, z) =
      stageLoopMap r W (stageTriangleRealization η θ hη hθ r (x, z)) q :=
  stageTriangleRealization_structure η θ hη hθ r z q x

-- Native barycentric simplex, with the literal three original faces.
example (r : ℕ) : C(stageSpace r V × Convexity.StdSimplex ℝ (Fin 3), stageSpace r W) :=
  stageTriangleBarycentric η θ hη hθ r

example (r : ℕ) (x : stageSpace r V) (t : unitInterval) :
    stageTriangleBarycentric η θ hη hθ r (x, triangleEdge 0 1 t) =
      stageTransformationTopHomotopy r η hη (t, x) :=
  stageTriangleBarycentric_first η θ hη hθ r x t

example (r : ℕ) (x : stageSpace r V) (t : unitInterval) :
    stageTriangleBarycentric η θ hη hθ r (x, triangleEdge 1 2 t) =
      stageTransformationTopHomotopy r θ hθ (t, x) :=
  stageTriangleBarycentric_second η θ hη hθ r x t

example (r : ℕ) (x : stageSpace r V) (t : unitInterval) :
    stageTriangleBarycentric η θ hη hθ r (x, triangleEdge 0 2 t) =
      stageTransformationTopHomotopy r (η ≫ θ)
        (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) (t, x) :=
  stageTriangleBarycentric_composite η θ hη hθ r x t

example (r : ℕ) (z : |(Δ[2] : SSet.{u})|) :
    stageTriangleRealization η θ hη hθ r (stagePoint r V, z) = stagePoint r W :=
  stageTriangleRealization_fixed_point η θ hη hθ r z

-- The actual continuous two-time comparison retains both endpoints and the whole zero line.
example (r : ℕ) : Continuous (stageTransformationCompositionHomotopy η θ hη hθ r) :=
  (stageTransformationCompositionHomotopy η θ hη hθ r).continuous

example (r : ℕ) (t : unitInterval) (x : stageSpace r V) :
    stageTransformationCompositionHomotopy η θ hη hθ r (0, (t, x)) =
      stageTransformationTopHomotopy r (η ≫ θ)
        (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) (t, x) :=
  (stageTransformationCompositionHomotopy η θ hη hθ r).apply_zero (t, x)

example (r : ℕ) (t : unitInterval) (x : stageSpace r V) :
    stageTransformationCompositionHomotopy η θ hη hθ r (1, (t, x)) =
      ((stageTransformationTopHomotopy r η hη).trans
        (stageTransformationTopHomotopy r θ hθ)) (t, x) :=
  (stageTransformationCompositionHomotopy η θ hη hθ r).apply_one (t, x)

-- The original concatenation uses the original half-interval parameterization.
example (r : ℕ) (t : unitInterval) (x : stageSpace r V) :
    stageTransformationCompositionHomotopy η θ hη hθ r (1, (t, x)) =
      if h : (t : ℝ) ≤ 1 / 2 then
        stageTransformationTopHomotopy r η hη
          (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩, x)
      else
        stageTransformationTopHomotopy r θ hθ
          (⟨2 * t - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩, x) := by
  rw [(stageTransformationCompositionHomotopy η θ hη hθ r).apply_one]
  exact ContinuousMap.Homotopy.trans_apply _ _ (t, x)

example (r : ℕ) (s : unitInterval) (x : stageSpace r V) :
    stageTransformationCompositionHomotopy η θ hη hθ r (s, (0, x)) =
      stageTransformationTopHomotopy r (η ≫ θ)
        (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) (0, x) :=
  (stageTransformationCompositionHomotopy η θ hη hθ r).eq_fst s (Or.inl rfl)

example (r : ℕ) (s : unitInterval) (x : stageSpace r V) :
    stageTransformationCompositionHomotopy η θ hη hθ r (s, (1, x)) =
      stageTransformationTopHomotopy r (η ≫ θ)
        (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) (1, x) :=
  (stageTransformationCompositionHomotopy η θ hη hθ r).eq_fst s (Or.inr (Or.inl rfl))

example (r : ℕ) (s t : unitInterval) :
    stageTransformationCompositionHomotopy η θ hη hθ r (s, (t, stagePoint r V)) =
      stagePoint r W := stageTransformationCompositionHomotopy_fixed_point η θ hη hθ r s t

example (r : ℕ) (s t q : unitInterval) (x : stageSpace r V) :
    stageTransformationCompositionHomotopy η θ hη hθ (r + 1)
        (s, (t, stageLoopMap r V x q)) =
      stageLoopMap r W (stageTransformationCompositionHomotopy η θ hη hθ r (s, (t, x))) q :=
  stageTransformationCompositionHomotopy_structure η θ hη hθ r s t q x

example : Continuous (transformationCompositionLoopFamily η θ hη hθ) :=
  (transformationCompositionLoopFamily η θ hη hθ).continuous

example (s t q : unitInterval) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    transformationCompositionLoopFamily η θ hη hθ (s, (t, γ)) q =
      stageTransformationCompositionHomotopy η θ hη hθ 0 (s, (t, γ q)) := rfl

example :
    (prespectrumTransformationHomotopy (η ≫ θ)
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A))).RelHomotopy
      ((prespectrumTransformationHomotopy η hη).trans
        (prespectrumTransformationHomotopy θ hθ)) :=
  prespectrumTransformationCompositionHomotopy η θ hη hθ

example (n : ℕ) (s t q : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).level (n + 1)
        (s, (t, (prespectrum V).structureMap n x q)) =
      (prespectrum W).structureMap n
        ((prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (s, (t, x))) q :=
  (prespectrumTransformationCompositionHomotopy η θ hη hθ).comm n s t x q

example (r : ℕ) (s t : unitInterval) (x : stageSpace r V) :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).level (r + 1) (s, (t, x)) =
      stageTransformationCompositionHomotopy η θ hη hθ r (s, (t, x)) := rfl

example (s t q : unitInterval) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      (prespectrumTransformationCompositionHomotopy η θ hη hθ).level 0 (s, (t, γ))) q =
      stageTransformationCompositionHomotopy η θ hη hθ 0 (s, (t, γ q)) := rfl

example (s : unitInterval) :
    LoopPrespectrum.Homotopy (prespectrumMap F) (prespectrumMap H) :=
  (prespectrumTransformationCompositionHomotopy η θ hη hθ).at s

example : (prespectrumTransformationCompositionHomotopy η θ hη hθ).at 0 =
    prespectrumTransformationHomotopy (η ≫ θ)
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) :=
  (prespectrumTransformationCompositionHomotopy η θ hη hθ).at_zero

example : (prespectrumTransformationCompositionHomotopy η θ hη hθ).at 1 =
    (prespectrumTransformationHomotopy η hη).trans (prespectrumTransformationHomotopy θ hθ) :=
  (prespectrumTransformationCompositionHomotopy η θ hη hθ).at_one

section OriginalUniverses

-- The dependency's arbitrary-exact normalization and KMap remain unchanged.
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (WC : Structure C) (WD : Structure D) {J K : C ⥤ D}
  (hJ : IsExact WC.cof WC.weq WD.cof WD.weq J)
  (hK : IsExact WC.cof WC.weq WD.cof WD.weq K)
  (α : J ⟶ K) (hα : ∀ A, WD.weq (α.app A))

example : exactOriginalPrespectrumMap WC WD hJ =
    originalPrespectrumMap WC WD hJ.rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) := rfl

example : LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap WC WD hJ)
    (exactOriginalPrespectrumMap WC WD hK) := exactOriginalPrespectrumHomotopy WC WD hJ hK α hα

example (n : ℕ) (a : WC.K n) :
    originalZeroSpaceEquiv WD n (KMap hJ n a) =
      HomotopyGroup.map ((exactOriginalPrespectrumMap WC WD hJ).map 0)
        ((exactOriginalPrespectrumMap WC WD hJ).map_point 0) (originalZeroSpaceEquiv WC n a) :=
  exactOriginalZeroSpaceEquiv_naturality WC WD hJ n a

end OriginalUniverses
end WaldhausenIteratedCompositionTests
