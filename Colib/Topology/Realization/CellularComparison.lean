/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.MonomorphismHEP
public import Colib.Topology.Realization.Skeleton
public import Colib.Topology.Homotopy.Equiv.IsoSquare
public import Colib.Topology.Homotopy.Equiv.Sigma
public import Colib.Topology.Pushout.HomotopyEquivalence
public import Colib.Topology.Category.TopCat.SequentialColimit.HomotopyInvariance
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-! A cellular criterion for natural realization equivalences. -/
/-! Implementation provenance: adapted from the matching Quillen file at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual simplicial relative
cell complex, coproduct and pushout comparisons, prescribed natural map and
sequential colimit are unchanged. No global realization equivalence is assumed.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.RealizationComparison
open TopCat

variable {F : SSet.{u} ⥤ SSet.{u}} (η : F ⟶ 𝟭 SSet.{u})

/-- A specified natural comparison is an actual realization homotopy equivalence. -/
def RealizesEquiv (X : SSet.{u}) : Prop :=
  ∃ E : ContinuousMap.HomotopyEquiv |F.obj X| |X|,
    E.toFun = (SSet.toTop.map (η.app X)).hom

lemma realization_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map (F.map f) ≫ SSet.toTop.map (η.app Y) =
      SSet.toTop.map (η.app X) ≫ SSet.toTop.map f := by
  have h := η.naturality f
  change F.map f ≫ η.app Y = η.app X ≫ f at h
  simpa only [Functor.map_comp] using congrArg SSet.toTop.map h

lemma realizesEquiv_of_iso {X Y : SSet.{u}} (e : X ≅ Y)
    (h : RealizesEquiv η X) : RealizesEquiv η Y := by
  obtain ⟨E, hE⟩ := h
  exact ⟨homotopyEquivOfIsoSquare _ _ (SSet.toTop.mapIso (F.mapIso e.symm))
    (SSet.toTop.mapIso e.symm)
    (realization_naturality η e.inv).symm E hE, rfl⟩

lemma realizesEquiv_initial [PreservesColimits F] {X : SSet.{u}}
    (hX : IsInitial X) : RealizesEquiv η X := by
  let : IsIso (η.app X) := isIso_of_isInitial (hX.isInitialObj F X) hX _
  exact ⟨(TopCat.homeoOfIso (SSet.toTop.mapIso (asIso (η.app X)))).toHomotopyEquiv, rfl⟩

lemma realizesEquiv_coproduct [PreservesColimits F] {ι : Type u}
    (X : ι → SSet.{u}) (c : Cofan X) (hc : IsColimit c)
    (h : ∀ i, RealizesEquiv η (X i)) : RealizesEquiv η c.pt := by
  choose E hE using h
  let a : Cofan (fun i ↦ |F.obj (X i)|) :=
    Cofan.mk |F.obj c.pt| (fun i ↦ SSet.toTop.map (F.map (c.inj i)))
  let b : Cofan (fun i ↦ |X i|) :=
    Cofan.mk |c.pt| (fun i ↦ SSet.toTop.map (c.inj i))
  have ha : IsColimit a := isColimitCofanMkObjOfIsColimit (F ⋙ SSet.toTop) X c.inj hc
  have hb : IsColimit b := isColimitCofanMkObjOfIsColimit SSet.toTop X c.inj hc
  let ea := ha.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit fun i ↦ |F.obj (X i)|)
  let eb := hb.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit fun i ↦ |X i|)
  let f : TopCat.of (Σ i, |F.obj (X i)|) ⟶ TopCat.of (Σ i, |X i|) :=
    TopCat.ofHom (ContinuousMap.sigmaContinuousMap fun i ↦ (SSet.toTop.map (η.app (X i))).hom)
  have w : SSet.toTop.map (η.app c.pt) ≫ eb.hom = ea.hom ≫ f := by
    apply ha.hom_ext
    intro ⟨i⟩
    change SSet.toTop.map (F.map (c.inj i)) ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp, η.naturality, Functor.map_comp,
      Category.assoc]
    change SSet.toTop.map (η.app (X i)) ≫ b.inj i ≫ eb.hom = a.inj i ≫ ea.hom ≫ f
    have haι : a.inj i ≫ ea.hom = TopCat.sigmaι (fun i ↦ |F.obj (X i)|) i :=
      ha.comp_coconePointUniqueUpToIso_hom _ ⟨i⟩
    have hbι : b.inj i ≫ eb.hom = TopCat.sigmaι (fun i ↦ |X i|) i :=
      hb.comp_coconePointUniqueUpToIso_hom _ ⟨i⟩
    rw [hbι, ← Category.assoc, haι]
    rfl
  exact ⟨homotopyEquivOfIsoSquare _ f ea eb w (ContinuousMap.sigmaHomotopyEquiv E)
    (by apply ContinuousMap.ext; intro x; change (⟨x.1, (E x.1).toFun x.2⟩ : Σ i, |X i|) = _; rw
      [hE]; rfl), rfl⟩

lemma realizesEquiv_pushout [PreservesColimits F] [F.PreservesMonomorphisms]
    {A B C D : SSet.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    [Mono i] (sq : IsPushout i f g j)
    (hA : RealizesEquiv η A) (hB : RealizesEquiv η B) (hC : RealizesEquiv η C) :
    RealizesEquiv η D := by
  obtain ⟨eA, heA⟩ := hA
  obtain ⟨eB, heB⟩ := hB
  obtain ⟨eC, heC⟩ := hC
  refine ⟨TopCat.Pushout.pushoutHomotopyEquivOfMap (sq.map (F ⋙ SSet.toTop)) (sq.map SSet.toTop)
    (SSet.homotopyExtensionProperty_realization_mono (F.map i))
    (SSet.homotopyExtensionProperty_realization_mono i)
    (SSet.toTop.map (η.app A)) (SSet.toTop.map (η.app B))
    (SSet.toTop.map (η.app C)) (SSet.toTop.map (η.app D))
    (realization_naturality η i) (realization_naturality η f)
    (realization_naturality η g) (realization_naturality η j)
    eA heA eB heB eC heC, rfl⟩

/-- The skeletal stages used by the actual simplicial relative cell complex. -/
abbrev stage (X : SSet.{u}) (n : ℕ) : SSet.{u} := (SSet.relativeCellComplex X).F.obj n

/-- A simplicial set of dimension less than `n` equals its `n`-stage. -/
def stageIsoOfDimension (X : SSet.{u}) (n : ℕ) [X.HasDimensionLT n] : stage X n ≅ X := by
  refine SSet.Subcomplex.eqToIso ?_ ≪≫ SSet.Subcomplex.topIso X
  change SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) n = ⊤
  rw [skeletonOfMono_bot]
  apply (SSet.Subcomplex.eq_top_iff_of_hasDimensionLT _ n).2
  intro i hi x hx
  exact X.mem_skeleton x hi

lemma realizesEquiv_stage [PreservesColimits F] [F.PreservesMonomorphisms]
    (hΔ : ∀ n, RealizesEquiv η (Δ[n] : SSet.{u})) (n : ℕ) :
    ∀ X : SSet.{u}, RealizesEquiv η (stage X n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X
    cases n with
    | zero =>
      apply realizesEquiv_initial
      exact SSet.Subcomplex.isInitialBot.ofIso (SSet.relativeCellComplex X).isoBot.symm
    | succ n =>
      let R := SSet.relativeCellComplex X
      let C := R.attachCells n (by simp)
      have hBdy : RealizesEquiv η (∂Δ[n] : SSet.{u}) :=
        realizesEquiv_of_iso η (stageIsoOfDimension _ n) (ih n (by omega) _)
      have hA : RealizesEquiv η C.cofan₁.pt :=
        realizesEquiv_coproduct η (fun _ : C.ι ↦ (∂Δ[n] : SSet.{u})) C.cofan₁
          C.isColimit₁ (fun _ ↦ hBdy)
      have hB : RealizesEquiv η C.cofan₂.pt :=
        realizesEquiv_coproduct η (fun _ : C.ι ↦ (Δ[n] : SSet.{u})) C.cofan₂
          C.isColimit₂ (fun _ ↦ hΔ n)
      let : Mono C.m := by dsimp [C, R]; infer_instance
      exact realizesEquiv_pushout η C.isPushout.flip hA hB (ih n (by omega) X)

/-- A cocontinuous, mono-preserving simplicial functor with a natural map to
identity gives an actual equivalence on every realization if it does so on
all representables. The proof glues actual homotopy inverses over the genuine
skeletal pushouts and their sequential colimit. -/
theorem realizesEquiv_all [PreservesColimits F] [PreservesColimitsOfShape ℕ F]
    [F.PreservesMonomorphisms]
    (hΔ : ∀ n, RealizesEquiv η (Δ[n] : SSet.{u})) (X : SSet.{u}) : RealizesEquiv η X := by
  let R := SSet.relativeCellComplex X
  let A := R.F ⋙ F ⋙ SSet.toTop
  let B := R.F ⋙ SSet.toTop
  let α : A ⟶ B := Functor.whiskerRight (Functor.whiskerLeft R.F η) SSet.toTop
  let c : Cocone A := (F ⋙ SSet.toTop).mapCocone (Cocone.mk X R.incl)
  let d : Cocone B := SSet.toTop.mapCocone (Cocone.mk X R.incl)
  have hc : IsColimit c := isColimitOfPreserves (F ⋙ SSet.toTop) R.isColimit
  have hd : IsColimit d := isColimitOfPreserves SSet.toTop R.isColimit
  have hmono (n : ℕ) : Mono (R.F.map (homOfLE (Nat.le_succ n))) := by
    change Mono (SSet.Subcomplex.homOfLE
      ((SSet.skeletonOfMono (⊥ : X.Subcomplex).ι).monotone (Nat.le_succ n)))
    infer_instance
  have hA (n : ℕ) : TopCat.HomotopyExtensionProperty (A.map (homOfLE (Nat.le_succ n))) := by
    let := hmono n
    exact SSet.homotopyExtensionProperty_realization_mono (F.map (R.F.map (homOfLE
      (Nat.le_succ n))))
  have hB (n : ℕ) : TopCat.HomotopyExtensionProperty (B.map (homOfLE (Nat.le_succ n))) := by
    let := hmono n
    exact SSet.homotopyExtensionProperty_realization_mono (R.F.map (homOfLE
      (Nat.le_succ n)))
  choose E hE using fun n ↦ realizesEquiv_stage η hΔ n X
  let e := sequentialCoconeHomotopyEquiv α hA hB E hE c hc d hd
  have he : e.toFun = (SSet.toTop.map (η.app X)).hom := by
    rw [sequentialCoconeHomotopyEquiv_toFun]
    apply congrArg TopCat.Hom.hom
    apply hc.hom_ext
    intro n
    rw [hc.ι_map]
    change SSet.toTop.map (η.app (R.F.obj n)) ≫ SSet.toTop.map (R.incl.app n) =
      SSet.toTop.map (F.map (R.incl.app n)) ≫ SSet.toTop.map (η.app X)
    exact (realization_naturality η (R.incl.app n)).symm
  exact ⟨e, he⟩

end SSet.RealizationComparison
