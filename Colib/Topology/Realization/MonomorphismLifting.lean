/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Skeleton
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# Lifting from realized simplex boundaries to all realized monomorphisms

The actual relative simplicial skeleton is a sequence of coproduct pushouts
of boundary inclusions. Right lifting against these compact generators
therefore extends over every realized simplicial monomorphism.
-/
/-! Implementation provenance: adapted from the matching Quillen file at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The stronger monomorphism-embedding
import is replaced by the already established actual relative-skeleton API.
The maps, lifting hypotheses, cell complex and all proofs are unchanged.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Topology
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet

/-- Lifting against a family glues over any specified actual coproduct cocones. -/
theorem hasLiftingProperty_of_coproductCofans
    {ι : Type u} {A B : ι → TopCat.{u}} (f : ∀ i, A i ⟶ B i)
    (a : Cofan A) (ha : IsColimit a) (b : Cofan B) (hb : IsColimit b)
    (m : a.pt ⟶ b.pt) (hm : ∀ i, a.inj i ≫ m = f i ≫ b.inj i)
    {E Y : TopCat.{u}} (p : E ⟶ Y) (hp : ∀ i, HasLiftingProperty (f i) p) :
    HasLiftingProperty m p where
  sq_hasLift {t r} sq := by
    let (i : ι) : HasLiftingProperty (f i) p := hp i
    have s (i : ι) : CommSq (a.inj i ≫ t) (f i) p (b.inj i ≫ r) := by
      constructor
      rw [Category.assoc, sq.w, ← Category.assoc, hm, Category.assoc]
    let l := Cofan.IsColimit.desc hb (fun i ↦ (s i).lift)
    have hl (i : ι) : b.inj i ≫ l = (s i).lift := Cofan.IsColimit.fac hb _ i
    refine ⟨l, ?_, ?_⟩
    · apply ha.hom_ext
      intro ⟨i⟩
      change a.inj i ≫ m ≫ l = a.inj i ≫ t
      rw [← Category.assoc, hm, Category.assoc, hl, CommSq.fac_left]
    · apply hb.hom_ext
      intro ⟨i⟩
      change b.inj i ≫ l ≫ p = b.inj i ≫ r
      rw [← Category.assoc, hl, CommSq.fac_right]

/-- Any map lifting against all actual realized simplex boundaries lifts
against every actual realized simplicial monomorphism. -/
theorem hasLiftingProperty_realization_mono
    {E Y : TopCat.{u}} (p : E ⟶ Y)
    (hp : ∀ n : ℕ, HasLiftingProperty (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u}))) p)
    {A X : SSet.{u}} (i : A ⟶ X) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i) p := by
  let R := SSet.relativeCellComplexOfMono i
  have hstep (n : ℕ) : HasLiftingProperty
      ((realizedRelativeSkeletonTower i).map (homOfLE (Nat.le_succ n))) p := by
    let C := R.attachCells n (by simp)
    let a : Cofan (fun k : C.ι ↦ SSet.toTop.obj (∂Δ[n] : SSet.{u})) :=
      Cofan.mk (SSet.toTop.obj C.cofan₁.pt) (fun k ↦ SSet.toTop.map (C.cofan₁.inj k))
    let b : Cofan (fun k : C.ι ↦ SSet.toTop.obj (Δ[n] : SSet.{u})) :=
      Cofan.mk (SSet.toTop.obj C.cofan₂.pt) (fun k ↦ SSet.toTop.map (C.cofan₂.inj k))
    have ha : IsColimit a := isColimitCofanMkObjOfIsColimit SSet.toTop _ _ C.isColimit₁
    have hb : IsColimit b := isColimitCofanMkObjOfIsColimit SSet.toTop _ _ C.isColimit₂
    have hm (k : C.ι) : a.inj k ≫ SSet.toTop.map C.m =
        SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})) ≫ b.inj k := by
      change SSet.toTop.map (C.cofan₁.inj k) ≫ SSet.toTop.map C.m = _
      rw [← Functor.map_comp, C.hm, Functor.map_comp]
      rfl
    let : HasLiftingProperty (SSet.toTop.map C.m) p :=
      hasLiftingProperty_of_coproductCofans (fun _ : C.ι ↦ SSet.toTop.map ∂Δ[n].ι)
        a ha b hb (SSet.toTop.map C.m) hm p (fun _ ↦ hp n)
    exact (C.isPushout.map SSet.toTop).hasLiftingProperty p
  let : HasLiftingProperty ((realizedRelativeSkeletonCocone i).ι.app 0) p :=
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := realizedRelativeSkeletonIsColimit i) (fun n _ ↦ hstep n)
  let e := SSet.toTop.mapIso R.isoBot
  have he : e.inv ≫ (realizedRelativeSkeletonCocone i).ι.app 0 = SSet.toTop.map i := by
    change SSet.toTop.map R.isoBot.inv ≫ SSet.toTop.map (R.incl.app 0) = _
    rw [← Functor.map_comp]
    exact congrArg SSet.toTop.map R.fac
  rw [← he]
  infer_instance

end SSet
