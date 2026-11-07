import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory MonoidalCategory SSet Topology
open scoped Simplicial Topology unitInterval

universe u v

namespace WaldhausenCoherentPrespectrumTests

section Generic

variable {E F G : LoopPrespectrum.{u}} {f g : E ⟶ F}
  (H : LoopPrespectrum.Homotopy f g) (h : F ⟶ G)

-- The generic owner retains actual continuous level maps, both time parameters, and base tracks.
example (n : ℕ) : C(unitInterval × E.space n, F.space n) := H.level n

example (n : ℕ) (x : E.space n) : H.level n (0, x) = f.map n x := H.at_zero n x

example (n : ℕ) (x : E.space n) : H.level n (1, x) = g.map n x := H.at_one n x

example (n : ℕ) (s : unitInterval) : H.level n (s, E.point n) = F.point n := H.at_point n s

example (n : ℕ) (s t : unitInterval) (x : E.space n) :
    H.level (n + 1) (s, E.structureMap n x t) =
      F.structureMap n (H.level n (s, x)) t := H.comm n s x t

example (s : unitInterval) : E ⟶ F := H.at s

example : H.at 0 = f := H.at_zero_eq

example : H.at 1 = g := H.at_one_eq

example : LoopPrespectrum.Homotopy f f := LoopPrespectrum.Homotopy.refl f

example : LoopPrespectrum.Homotopy (f ≫ h) (g ≫ h) := H.postcomp h

example {D : LoopPrespectrum.{u}} (j : D ⟶ E) :
    LoopPrespectrum.Homotopy (j ≫ f) (j ≫ g) := H.precomp j

example (n : ℕ) : (f.map n).HomotopyRel (g.map n) {E.point n} := H.levelHomotopy n

example (n k : ℕ) :
    HomotopyGroup.map (N := Fin k) (f.map n) (f.map_point n) =
      HomotopyGroup.map (g.map n) (g.map_point n) := H.homotopyGroupMap_eq n k

end Generic

section ActualStages

variable {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))

example (r : ℕ) : (stages r).obj V ⊗ Δ[1] ⟶ (stages r).obj W :=
  stageTransformationCylinder r η hη

example (r : ℕ) : SSet.Homotopy ((stages r).map F) ((stages r).map G) :=
  stageTransformationHomotopy r η hη

example (r : ℕ) (s : unitInterval) :
    stageTransformationTopHomotopy r η hη (s, stagePoint r V) = stagePoint r W :=
  stageTransformationTopHomotopy_fixed_point r η hη s

example (r : ℕ) (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n)
    (τ θ : (Δ[1]).obj n) :
    stageTransformationFunction (r + 1) η hη n ((stageCylinder r V).app n (A, τ)) θ =
      (stageCylinder r W).app n (stageTransformationFunction r η hη n A θ, τ) :=
  stageTransformationFunction_structure r η hη n A τ θ

example (r : ℕ) (s t : unitInterval) (x : stageSpace r V) :
    stageTransformationTopHomotopy (r + 1) η hη (s, stageLoopMap r V x t) =
      stageLoopMap r W (stageTransformationTopHomotopy r η hη (s, x)) t :=
  stageTransformationTopHomotopy_structure r η hη s t x

example : LoopPrespectrum.Homotopy (prespectrumMap F) (prespectrumMap G) :=
  prespectrumTransformationHomotopy η hη

example (r : ℕ) : (prespectrumTransformationHomotopy η hη).level (r + 1) =
    (stageTransformationTopHomotopy r η hη).toContinuousMap := rfl

example : (prespectrumTransformationHomotopy η hη).level 0 =
    transformationLoopHomotopy η hη := rfl

example (s t : unitInterval) (p : Path (stagePoint 0 V) (stagePoint 0 V)) :
    transformationLoopHomotopy η hη (s, p) t =
      stageTransformationTopHomotopy 0 η hη (s, p t) := rfl

end ActualStages

section OriginalUniverses

-- Object and morphism universes are independent. No zero-image equality is assumed here.
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F G : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A))

example : originalPrespectrum W ⟶ originalPrespectrum V := exactOriginalPrespectrumMap W V hF

example : exactOriginalPrespectrumMap W V hF =
    originalPrespectrumMap W V hF.rebase (rebaseFunctor_obj_base _ _ _ _) := rfl

example (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv V n (KMap hF n a) =
      HomotopyGroup.map ((exactOriginalPrespectrumMap W V hF).map 0)
        ((exactOriginalPrespectrumMap W V hF).map_point 0) (originalZeroSpaceEquiv W n a) :=
  exactOriginalZeroSpaceEquiv_naturality W V hF n a

example (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero) :
    LoopPrespectrum.Homotopy (originalPrespectrumMap W V hF h0F)
      (originalPrespectrumMap W V hG h0G) :=
  originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη

example : LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W V hF)
    (exactOriginalPrespectrumMap W V hG) := exactOriginalPrespectrumHomotopy W V hF hG η hη

example (e : F ≅ G) : LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W V hF)
    (exactOriginalPrespectrumMap W V hG) := exactOriginalPrespectrumIsoHomotopy W V hF hG e

example (n : ℕ) (s : unitInterval) :
    (exactOriginalPrespectrumHomotopy W V hF hG η hη).level n
      (s, (originalPrespectrum W).point n) = (originalPrespectrum V).point n :=
  (exactOriginalPrespectrumHomotopy W V hF hG η hη).at_point n s

example (n : ℕ) (s t : unitInterval) (x : (originalPrespectrum W).space n) :
    (exactOriginalPrespectrumHomotopy W V hF hG η hη).level (n + 1)
        (s, (originalPrespectrum W).structureMap n x t) =
      (originalPrespectrum V).structureMap n
        ((exactOriginalPrespectrumHomotopy W V hF hG η hη).level n (s, x)) t :=
  (exactOriginalPrespectrumHomotopy W V hF hG η hη).comm n s x t

-- The coherent zero-level homotopy itself recovers equality of the original KMap.
example (n : ℕ) : KMap hF n = KMap hG n := by
  ext a
  apply (originalZeroSpaceEquiv V n).injective
  rw [exactOriginalZeroSpaceEquiv_naturality W V hF,
    exactOriginalZeroSpaceEquiv_naturality W V hG]
  exact congrFun ((exactOriginalPrespectrumHomotopy W V hF hG η hη).homotopyGroupMap_eq 0 n)
    (originalZeroSpaceEquiv W n a)

end OriginalUniverses

end WaldhausenCoherentPrespectrumTests
