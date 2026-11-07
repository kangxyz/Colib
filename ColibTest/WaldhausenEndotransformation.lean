import Colib.KTheory.Waldhausen.Cofinality.EndotransformationHomotopy

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval

universe u v w

namespace WaldhausenEndotransformationTests

section Small

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
  (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
  (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A))

-- The actual zero endotransformation absorbs before any realization is taken.
example (A : V.obj.Obj) : (zeroEndotransformation F).app A =
    W.obj.waldhausen.isZero.from_ (F.hom.toFunctor.obj A) ≫
      W.obj.waldhausen.isZero.to_ (F.hom.toFunctor.obj A) := rfl

example {A B : V.obj.Obj} (f : A ⟶ B) :
    F.hom.toFunctor.map f ≫ (zeroEndotransformation F).app B =
      (zeroEndotransformation F).app A ≫ F.hom.toFunctor.map f :=
  (zeroEndotransformation F).naturality f

example : η ≫ zeroEndotransformation F = zeroEndotransformation F :=
  zeroEndotransformation_absorb F η

example :
    (prespectrumTransformationHomotopy (zeroEndotransformation F) hz).RelHomotopy
      ((prespectrumTransformationHomotopy η hη).trans
        (prespectrumTransformationHomotopy (zeroEndotransformation F) hz)) :=
  prespectrumEndotransformationAbsorptionTriangle F η hη hz

-- The zero homotopy is a self-track of the same map, not a map to the zero target.
example : Homotopy (prespectrumMap F) (prespectrumMap F) :=
  prespectrumTransformationHomotopy (zeroEndotransformation F) hz

example : (prespectrumTransformationHomotopy η hη).RelHomotopy
    (Homotopy.refl (prespectrumMap F)) := prespectrumEndotransformationContraction F η hη hz

example : (prespectrumEndotransformationContraction F η hη hz).at 0 =
    prespectrumTransformationHomotopy η hη :=
  (prespectrumEndotransformationContraction F η hη hz).at_zero

example : (prespectrumEndotransformationContraction F η hη hz).at 1 =
    Homotopy.refl (prespectrumMap F) :=
  (prespectrumEndotransformationContraction F η hη hz).at_one

example (n : ℕ) : Continuous ((prespectrumEndotransformationContraction F η hη hz).level n) :=
  ((prespectrumEndotransformationContraction F η hη hz).level n).continuous

example (n : ℕ) (r : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction F η hη hz).level n (r, (0, x)) =
      (prespectrumMap F).map n x :=
  ((prespectrumEndotransformationContraction F η hη hz).at r).at_zero n x

example (n : ℕ) (r : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction F η hη hz).level n (r, (1, x)) =
      (prespectrumMap F).map n x :=
  ((prespectrumEndotransformationContraction F η hη hz).at r).at_one n x

example (n : ℕ) (r s : unitInterval) :
    (prespectrumEndotransformationContraction F η hη hz).level n
        (r, (s, (prespectrum V).point n)) = (prespectrum W).point n :=
  ((prespectrumEndotransformationContraction F η hη hz).at r).at_point n s

-- Comparison, original track, structure, and level-zero loop coordinates stay independent.
example (n : ℕ) (r s t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction F η hη hz).level (n + 1)
        (r, (s, (prespectrum V).structureMap n x t)) =
      (prespectrum W).structureMap n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) t :=
  (prespectrumEndotransformationContraction F η hη hz).comm n r s x t

example (r s q : unitInterval) (γ : (prespectrum V).space 0) :
    (prespectrumEndotransformationContraction F η hη hz).level (0 + 1)
        (r, (s, (prespectrum V).structureMap 0 γ q)) =
      (prespectrum W).structureMap 0
        ((prespectrumEndotransformationContraction F η hη hz).level 0 (r, (s, γ))) q :=
  (prespectrumEndotransformationContraction F η hη hz).comm 0 r s γ q

example (γ : Path (stagePoint 0 V) (stagePoint 0 V)) (q : unitInterval) :
    (prespectrum V).structureMap 0 γ q = γ q := rfl

end Small

section OriginalUniverses

-- No equality between the independent object, hom, or grade universes is assumed.
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} {G : Type w} [AddCommGroup G]
  (d : Cofinality.Grading V G) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq d.coarseStructure.cof d.coarseStructure.weq F) (η : F ⟶ F)

example (A : D) : d.coarseStructure.weq (V.isZero.from_ A ≫ V.isZero.to_ A) := rfl

example : (exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
    (fun _ ↦ rfl)).RelHomotopy
      (Homotopy.refl (exactOriginalPrespectrumMap W d.coarseStructure hF)) :=
  d.exactEndotransformationContraction W hF η

example : (d.exactEndotransformationContraction W hF η).at 0 =
    exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η (fun _ ↦ rfl) :=
  (d.exactEndotransformationContraction W hF η).at_zero

example : (d.exactEndotransformationContraction W hF η).at 1 =
    Homotopy.refl (exactOriginalPrespectrumMap W d.coarseStructure hF) :=
  (d.exactEndotransformationContraction W hF η).at_one

example (n : ℕ) (r : unitInterval) (x : (originalPrespectrum W).space n) :
    (d.exactEndotransformationContraction W hF η).level n (r, (0, x)) =
      (exactOriginalPrespectrumMap W d.coarseStructure hF).map n x :=
  ((d.exactEndotransformationContraction W hF η).at r).at_zero n x

example (n : ℕ) (r : unitInterval) (x : (originalPrespectrum W).space n) :
    (d.exactEndotransformationContraction W hF η).level n (r, (1, x)) =
      (exactOriginalPrespectrumMap W d.coarseStructure hF).map n x :=
  ((d.exactEndotransformationContraction W hF η).at r).at_one n x

example (n : ℕ) (r s : unitInterval) :
    (d.exactEndotransformationContraction W hF η).level n
        (r, (s, (originalPrespectrum W).point n)) =
      (originalPrespectrum d.coarseStructure).point n :=
  ((d.exactEndotransformationContraction W hF η).at r).at_point n s

example (n : ℕ) (r s t : unitInterval) (x : (originalPrespectrum W).space n) :
    (d.exactEndotransformationContraction W hF η).level (n + 1)
        (r, (s, (originalPrespectrum W).structureMap n x t)) =
      (originalPrespectrum d.coarseStructure).structureMap n
        ((d.exactEndotransformationContraction W hF η).level n (r, (s, x))) t :=
  (d.exactEndotransformationContraction W hF η).comm n r s x t

-- Canonical exact-functor normalization and the original public K-map are unchanged.
example : exactOriginalPrespectrumMap W d.coarseStructure hF =
    originalPrespectrumMap W d.coarseStructure hF.rebase
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) := rfl

example (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv d.coarseStructure n (KMap hF n a) =
      HomotopyGroup.map ((exactOriginalPrespectrumMap W d.coarseStructure hF).map 0)
        ((exactOriginalPrespectrumMap W d.coarseStructure hF).map_point 0)
        (originalZeroSpaceEquiv W n a) :=
  exactOriginalZeroSpaceEquiv_naturality W d.coarseStructure hF n a

variable {T : LoopPrespectrum.{max u v}} (j : originalPrespectrum d.coarseStructure ⟶ T)
  (N : Homotopy (exactOriginalPrespectrumMap W d.coarseStructure hF ≫ j)
    (zeroHom (originalPrespectrum W) T))

-- The prescribed conjugate contains both original null legs, in their exact order.
example : ((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
    (fun _ ↦ rfl)).postcomp j).conjugateToZero N =
      N.symm.trans (((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
        (fun _ ↦ rfl)).postcomp j).trans N) := rfl

example (n : ℕ) (s : unitInterval) (x : (originalPrespectrum W).space n) :
    Path.toContinuousMap ((((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
        (fun _ ↦ rfl)).postcomp j).nullLoopMap N).map n x) s =
      (N.symm.trans (((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
        (fun _ ↦ rfl)).postcomp j).trans N)).level n (s, x) := rfl

example : Homotopy (((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
    (fun _ ↦ rfl)).postcomp j).nullLoopMap N)
      (zeroHom (originalPrespectrum W) (parameterLooping T)) :=
  d.exactEndotransformationNullLoopHomotopy W hF η j N

example (n : ℕ) (x : (originalPrespectrum W).space n) :
    (d.exactEndotransformationNullLoopHomotopy W hF η j N).level n (0, x) =
      (((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
        (fun _ ↦ rfl)).postcomp j).nullLoopMap N).map n x :=
  (d.exactEndotransformationNullLoopHomotopy W hF η j N).at_zero n x

example (n : ℕ) (x : (originalPrespectrum W).space n) :
    (d.exactEndotransformationNullLoopHomotopy W hF η j N).level n (1, x) =
      Path.refl (T.point n) :=
  (d.exactEndotransformationNullLoopHomotopy W hF η j N).at_one n x

example (n : ℕ) (r : unitInterval) :
    (d.exactEndotransformationNullLoopHomotopy W hF η j N).level n
        (r, (originalPrespectrum W).point n) = Path.refl (T.point n) :=
  (d.exactEndotransformationNullLoopHomotopy W hF η j N).at_point n r

-- No loop-coordinate transpose is silently dropped from the structure square.
example (n : ℕ) (r s t : unitInterval) (x : (originalPrespectrum W).space n) :
    let H := d.exactEndotransformationNullLoopHomotopy W hF η j N
    Path.toContinuousMap (H.level (n + 1)
        (r, (originalPrespectrum W).structureMap n x t)) s =
      T.structureMap n (Path.toContinuousMap (H.level n (r, x)) s) t := by
  intro H
  exact congrArg (fun γ : Path (T.point (n + 1)) (T.point (n + 1)) ↦ γ s)
    (H.comm n r x t)

example (n : ℕ) :
    let H := d.exactEndotransformationNullLoopHomotopy W hF η j N
    Continuous (fun z : unitInterval × (unitInterval × (originalPrespectrum W).space n) ↦
      Path.toContinuousMap (H.level n (z.1, z.2.2)) z.2.1) := by
  intro H
  have h : Continuous (fun z : (unitInterval × (originalPrespectrum W).space n) ×
      unitInterval ↦ Path.toContinuousMap (H.level n z.1) z.2) :=
    Path.continuous_uncurry_iff.mpr (H.level n).continuous
  exact h.comp ((continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst)

end OriginalUniverses
end WaldhausenEndotransformationTests
