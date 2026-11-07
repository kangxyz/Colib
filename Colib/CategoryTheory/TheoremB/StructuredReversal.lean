/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.Opposite
public import Colib.CategoryTheory.TheoremB.Naturality

/-! Opposite categories reverse the structure-arrow homotopy. -/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredReversal.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

noncomputable section
open SSet TopCat Topology CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB

/-- Reverse both the simplicial source and interval coordinates. -/
def oppositeCylinderMap (X : SSet.{u}) : X.op ⊗ Δ[1] ⟶ (X ⊗ Δ[1]).op :=
  (𝟙 X.op) ⊗ₘ (SSet.stdSimplex.opIso ⦋1⦌).inv

@[simp] theorem oppositeCylinderMap_fst (X : SSet.{u}) :
    oppositeCylinderMap X ≫ SSet.opFunctor.map (fst X Δ[1]) = fst X.op Δ[1] := by
  ext n z : 4
  rfl

@[simp] theorem oppositeCylinderMap_snd (X : SSet.{u}) :
    oppositeCylinderMap X ≫ SSet.opFunctor.map (snd X Δ[1]) =
      snd X.op Δ[1] ≫ (SSet.stdSimplex.opIso ⦋1⦌).inv := by
  ext n z : 4
  rfl

private theorem pointOfConstSquare {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : TopCat.const x ≫ f = f ≫ TopCat.const y) : f x = y :=
  ConcreteCategory.congr_hom h x

/-- Opposite realization preserves every simplicial vertex. -/
theorem realizationOpposite_point (X : SSet.{u}) (x : X _⦋0⦌) :
    (realizationOppositeNatIso.app X).hom (realizationPoint (SSet.opObjEquiv.symm x)) =
      realizationPoint x := by
  have hc : SSet.opFunctor.map (SSet.const x : X ⟶ X) =
      SSet.const (SSet.opObjEquiv.symm x) := by
    ext n z : 4
    rfl
  have hr {A B : SSet.{u}} (b : B _⦋0⦌) :
      SSet.toTop.map (SSet.const b : A ⟶ B) = TopCat.const (realizationPoint b) := by
    ext z : 1
    exact realization_const_apply b z
  apply pointOfConstSquare
  have h := realizationOpposite_naturality (SSet.const x : X ⟶ X)
  rw [hc, hr, hr] at h
  exact h

/-- The interval-coordinate map produced by actual opposite realization. -/
def oppositeRealizationInterval : TopCat.I.{u} ⟶ TopCat.I.{u} :=
  SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map (SSet.stdSimplex.opIso ⦋1⦌).inv ≫
    (realizationOppositeNatIso.app (Δ[1] : SSet.{u})).hom ≫ SSet.stdSimplex.toTopObjIsoI.hom

private theorem oppositeInterval_vertex (i : Fin 2) :
    ((SSet.stdSimplex.opIso ⦋1⦌).inv.app (op ⦋0⦌))
        (SSet.stdSimplex.obj₀Equiv.symm i) =
      SSet.opObjEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm i.rev) := by
  apply SSet.opObjEquiv.injective
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j
  rfl

@[simp] theorem oppositeRealizationInterval_zero :
    oppositeRealizationInterval (0 : TopCat.I.{u}) = 1 := by
  have hEndpoint : SSet.stdSimplex.toTopObjIsoI.hom
      (realizationPoint (SSet.stdSimplex.obj₀Equiv.{u}.symm 0)) =
        (0 : TopCat.I) := by
    simpa only [SSet.stdSimplex.obj₀Equiv_symm_apply] using
      realizationIntervalIso_zero_const
  change SSet.stdSimplex.toTopObjIsoI.hom
    ((realizationOppositeNatIso.app (Δ[1] : SSet.{u})).hom
      (SSet.toTop.map (SSet.stdSimplex.opIso ⦋1⦌).inv
        (SSet.stdSimplex.toTopObjIsoI.inv 0))) = 1
  rw [← hEndpoint, Iso.hom_inv_id_apply,
    realizationPoint_naturality, oppositeInterval_vertex,
    realizationOpposite_point]
  simpa only [show (0 : Fin 2).rev = 1 from rfl,
    SSet.stdSimplex.obj₀Equiv_symm_apply] using realizationIntervalIso_one_const

@[simp] theorem oppositeRealizationInterval_one :
    oppositeRealizationInterval (1 : TopCat.I.{u}) = 0 := by
  have hEndpoint : SSet.stdSimplex.toTopObjIsoI.hom
      (realizationPoint (SSet.stdSimplex.obj₀Equiv.{u}.symm 1)) =
        (1 : TopCat.I) := by
    simpa only [SSet.stdSimplex.obj₀Equiv_symm_apply] using
      realizationIntervalIso_one_const
  change SSet.stdSimplex.toTopObjIsoI.hom
    ((realizationOppositeNatIso.app (Δ[1] : SSet.{u})).hom
      (SSet.toTop.map (SSet.stdSimplex.opIso ⦋1⦌).inv
        (SSet.stdSimplex.toTopObjIsoI.inv 1))) = 0
  rw [← hEndpoint, Iso.hom_inv_id_apply,
    realizationPoint_naturality, oppositeInterval_vertex,
    realizationOpposite_point]
  simpa only [show (1 : Fin 2).rev = 0 from rfl,
    SSet.stdSimplex.obj₀Equiv_symm_apply] using realizationIntervalIso_zero_const

/-- Opposite realization on the cylinder separates into its source and
interval maps, by the two product projections. -/
theorem oppositeCylinder_realization (X : SSet.{u}) :
    SSet.toTop.map (oppositeCylinderMap X) ≫
      (realizationOppositeNatIso.app (X ⊗ Δ[1])).hom ≫
        (realizationCylinderIso X).hom =
    (realizationCylinderIso X.op).hom ≫
      ((realizationOppositeNatIso.app X).hom ⊗ₘ oppositeRealizationInterval) := by
  change SSet.toTop.map (oppositeCylinderMap X) ≫
      (realizationOppositeNatIso.app (X ⊗ Δ[1])).hom ≫
        realizationCylinderComparison X =
      realizationCylinderComparison X.op ≫
        ((realizationOppositeNatIso.app X).hom ⊗ₘ oppositeRealizationInterval)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, realizationCylinderComparison_fst, tensorHom_fst]
    rw [← realizationOpposite_naturality, ← Category.assoc, ← SSet.toTop.map_comp,
      oppositeCylinderMap_fst]
    rw [← Category.assoc, realizationCylinderComparison_fst]
  · simp only [Category.assoc, realizationCylinderComparison_snd, tensorHom_snd]
    rw [← Category.assoc (realizationOppositeNatIso.app (X ⊗ Δ[1])).hom,
      ← realizationOpposite_naturality]
    simp only [← Category.assoc]
    rw [← SSet.toTop.map_comp, oppositeCylinderMap_snd, SSet.toTop.map_comp]
    simp [realizationCylinderComparison, oppositeRealizationInterval, Category.assoc]

@[reassoc] theorem oppositeCylinder_realization_inv (X : SSet.{u}) :
    (realizationCylinderIso X.op).inv ≫ SSet.toTop.map (oppositeCylinderMap X) ≫
      (realizationOppositeNatIso.app (X ⊗ Δ[1])).hom =
    ((realizationOppositeNatIso.app X).hom ⊗ₘ oppositeRealizationInterval) ≫
      (realizationCylinderIso X).inv := by
  apply (cancel_mono (realizationCylinderIso X).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [oppositeCylinder_realization]
  simp

/-- Convex interpolation stays inside the ordinary unit interval. -/
def intervalInterpolate (s a b : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ), by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.2.2) a.2.1) (mul_nonneg s.2.1 b.2.1)
    · calc
        (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ) ≤
            (1 - (s : ℝ)) * 1 + (s : ℝ) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left a.2.2 (sub_nonneg.mpr s.2.2))
            (mul_le_mul_of_nonneg_left b.2.2 s.2.1)
        _ = 1 := by ring⟩

@[fun_prop] theorem continuous_intervalInterpolate :
    Continuous (fun z : unitInterval × unitInterval × unitInterval ↦
      intervalInterpolate z.1 z.2.1 z.2.2) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem intervalInterpolate_zero (a b : unitInterval) :
    intervalInterpolate 0 a b = a := by ext; simp [intervalInterpolate]
@[simp] theorem intervalInterpolate_one (a b : unitInterval) :
    intervalInterpolate 1 a b = b := by ext; simp [intervalInterpolate]
@[simp] theorem intervalInterpolate_self (s a : unitInterval) :
    intervalInterpolate s a a = a := by ext; dsimp [intervalInterpolate]; ring

/-- The opposite realization interval map as a path from one to zero. -/
def oppositeIntervalPath : Path (1 : unitInterval) 0 where
  toFun t := (oppositeRealizationInterval.{u} (ULift.up t)).down
  continuous_toFun := continuous_uliftDown.comp
    (oppositeRealizationInterval.hom.continuous.comp continuous_uliftUp)
  source' := congrArg ULift.down oppositeRealizationInterval_zero
  target' := congrArg ULift.down oppositeRealizationInterval_one

/-- Ordinary time reflection as a path from one to zero. -/
def reversedIntervalPath : Path (1 : unitInterval) 0 where
  toFun := unitInterval.symm
  continuous_toFun := unitInterval.continuous_symm
  source' := unitInterval.symm_zero
  target' := unitInterval.symm_one

/-- The actual opposite interval map is homotopic to ordinary time reflection,
relative to both endpoints, by convex interpolation. -/
def oppositeIntervalHomotopy : oppositeIntervalPath.{u}.Homotopy reversedIntervalPath where
  toFun z := intervalInterpolate z.1 (oppositeIntervalPath z.2) (reversedIntervalPath z.2)
  continuous_toFun := continuous_intervalInterpolate.comp
    (continuous_fst.prodMk ((oppositeIntervalPath.continuous.comp continuous_snd).prodMk
      (reversedIntervalPath.continuous.comp continuous_snd)))
  map_zero_left _ := intervalInterpolate_zero _ _
  map_one_left _ := intervalInterpolate_one _ _
  prop' s t ht := by
    rcases ht with ht | ht
    · subst t
      simp
    · rw [Set.mem_singleton_iff] at ht
      subst t
      simp

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G : C ⥤ D}

/-- Reverse the categorical interval and the category simultaneously. -/
def intervalOppositeProductFunctor : Fin 2 × Cᵒᵖ ⥤ (Fin 2 × C)ᵒᵖ where
  obj X := op (X.1.rev, X.2.unop)
  map f := (show (_, _) ⟶ (_, _) from
    (homOfLE (Fin.rev_le_rev.mpr (leOfHom f.1)), f.2.unop)).op

/-- Categorical interval reversal carries the opposite transformation. -/
theorem naturalTransformationCylinderFunctor_op (α : F ⟶ G) :
    naturalTransformationCylinderFunctor (NatTrans.op α) =
      intervalOppositeProductFunctor ⋙ (naturalTransformationCylinderFunctor α).op := by
  refine CategoryTheory.Functor.hext (fun X ↦ ?_) ?_
  · rcases X with ⟨i, x⟩
    fin_cases i <;> rfl
  · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨f, g⟩
    have hij := leOfHom f
    fin_cases i <;> fin_cases j
    · simp [naturalTransformationCylinderFunctor, intervalOppositeProductFunctor,
        Functor.uncurry, ComposableArrows.mk₁]
    · simp only [naturalTransformationCylinderFunctor, intervalOppositeProductFunctor,
        Functor.uncurry, ComposableArrows.mk₁]
      exact heq_of_eq (congrArg Quiver.Hom.op (α.naturality g.unop))
    · exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) hij |>.elim
    · simp [naturalTransformationCylinderFunctor, intervalOppositeProductFunctor,
        Functor.uncurry, ComposableArrows.mk₁]

private theorem reversePairMap_heq {n : ℕ} (p : Fin (n + 1) → Fin 2)
    (c : ComposableArrows Cᵒᵖ n) {i j i' j' : Fin (n + 1)}
    (hi : i = i') (hj : j = j') (f : i ⟶ j) (g : i' ⟶ j')
    (a : (p j).rev ⟶ (p i).rev) (b : (p j').rev ⟶ (p i').rev) :
    (show (op ((p i).rev, (c.obj i).unop) : (Fin 2 × C)ᵒᵖ) ⟶
      op ((p j).rev, (c.obj j).unop) from Quiver.Hom.op (show ((p j).rev, (c.obj j).unop) ⟶ ((p
        i).rev, (c.obj i).unop) from
        (a, (c.map f).unop))) ≍
    (show (op ((p i').rev, (c.obj i').unop) : (Fin 2 × C)ᵒᵖ) ⟶
      op ((p j').rev, (c.obj j').unop) from Quiver.Hom.op (show ((p j').rev, (c.obj j').unop) ⟶ ((p
        i').rev, (c.obj i').unop) from
        (b, (c.map g).unop))) := by
  subst i'
  subst j'
  have hf : f = g := Subsingleton.elim _ _
  have ha : a = b := Subsingleton.elim _ _
  subst g
  subst b
  rfl

/-- The opposite natural transformation has the reversed nerve cylinder. -/
theorem naturalTransformationNerveCylinder_op (α : F ⟶ G) :
    naturalTransformationNerveCylinder (NatTrans.op α) =
      (nerveOppositeIso (C := C)).inv ▷ Δ[1] ≫
        oppositeCylinderMap (nerve C) ≫
          SSet.opFunctor.map (naturalTransformationNerveCylinder α) ≫
            (nerveOppositeIso (C := D)).hom := by
  ext n z : 4
  change (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
    naturalTransformationCylinderFunctor (NatTrans.op α) =
    reverseChain
      (((((SSet.stdSimplex.opIso ⦋1⦌).inv.app n) z.2).down.toOrderHom.monotone.functor.prod'
        (unreverseChain z.1)) ⋙ naturalTransformationCylinderFunctor α)
  rw [naturalTransformationCylinderFunctor_op]
  change ((z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
    intervalOppositeProductFunctor) ⋙ (naturalTransformationCylinderFunctor α).op =
      (reverseChain
        ((((SSet.stdSimplex.opIso ⦋1⦌).inv.app n) z.2).down.toOrderHom.monotone.functor.prod'
          (unreverseChain z.1))) ⋙ (naturalTransformationCylinderFunctor α).op
  congr 1
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · change op ((z.2.down.toOrderHom i).rev, (z.1.obj i).unop) =
      op ((z.2.down.toOrderHom i.rev.rev).rev, (z.1.obj i.rev.rev).unop)
    simp
  · intro i j f
    dsimp [Functor.prod', intervalOppositeProductFunctor,
      reverseChain, unreverseChain]
    exact reversePairMap_heq z.2.down.toOrderHom z.1
      (Fin.rev_rev i).symm (Fin.rev_rev j).symm _ _ _ _
/-- The realized opposite natural transformation commutes with the source
opposite map and the actual opposite interval parameter. -/
theorem naturalTransformationCylinder_op_realization (α : F ⟶ G) :
    SSet.toTop.map (naturalTransformationNerveCylinder (NatTrans.op α)) ≫
      (classifyingOppositeIso D).hom =
    SSet.toTop.map ((nerveOppositeIso (C := C)).inv ▷ Δ[1]) ≫
      SSet.toTop.map (oppositeCylinderMap (nerve C)) ≫
        (realizationOppositeNatIso.app (nerve C ⊗ Δ[1])).hom ≫
          SSet.toTop.map (naturalTransformationNerveCylinder α) := by
  rw [naturalTransformationNerveCylinder_op]
  simp only [Functor.map_comp, Category.assoc]
  change _ ≫ _ ≫ _ ≫ SSet.toTop.map (nerveOppositeIso (C := D)).hom ≫
    SSet.toTop.map (nerveOppositeIso (C := D)).inv ≫
      (realizationOppositeNatIso.app (nerve D)).hom = _
  rw [← Category.assoc (SSet.toTop.map (nerveOppositeIso (C := D)).hom),
    ← SSet.toTop.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    realizationOpposite_naturality]

private theorem cylinderSquare_apply {A B C X Y Z W : TopCat.{u}}
    (i₀ : A ⊗ TopCat.I ⟶ X) (m : X ⟶ Y) (p : Y ⟶ Z)
    (a : A ⟶ B) (b : B ⟶ C) (r : TopCat.I ⟶ TopCat.I)
    (i : C ⊗ TopCat.I ⟶ W) (n : W ⟶ Z)
    (h : i₀ ≫ m ≫ p = a ▷ TopCat.I ≫ (b ⊗ₘ r) ≫ i ≫ n)
    (x : A) (t : TopCat.I) :
    p (m (i₀ (x, t))) = n (i (b (a x), r t)) :=
  ConcreteCategory.congr_hom h (x, t)

private theorem classifyingHomotopy_apply (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy α (t, x) =
      SSet.toTop.map (naturalTransformationNerveCylinder α)
        ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) := rfl

private theorem oppositeIso_apply (x : ClassifyingSpace Cᵒᵖ) :
    (classifyingOppositeIso C).hom x = (realizationOppositeNatIso.app (nerve C)).hom
      (SSet.toTop.map (nerveOppositeIso (C := C)).inv x) := by
  dsimp only [ClassifyingSpace, CategoryTheory.Functor.comp_obj] at x ⊢
  rw [classifyingOppositeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_inv, TopCat.comp_app]

/-- Pointwise opposite-homotopy compatibility with its actual interval map. -/
theorem classifyingNaturalTransformationHomotopy_op (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace Cᵒᵖ) :
    (classifyingOppositeIso D).hom
      (classifyingSpaceNaturalTransformationHomotopy (NatTrans.op α) (t, x)) =
    classifyingSpaceNaturalTransformationHomotopy α
      ((oppositeRealizationInterval.{u} (ULift.up t)).down, (classifyingOppositeIso C).hom x) := by
  have h := congrArg (fun k ↦ (realizationCylinderIso (nerve Cᵒᵖ)).inv ≫ k)
    (naturalTransformationCylinder_op_realization α)
  simp only [← Category.assoc] at h
  rw [realizationCylinderIso_inv_naturality] at h
  simp only [Category.assoc] at h
  rw [oppositeCylinder_realization_inv_assoc] at h
  have hp := cylinderSquare_apply _ _ _ _ _ _ _ _ h x (ULift.up t)
  rw [classifyingHomotopy_apply, classifyingHomotopy_apply, oppositeIso_apply (C := C),
    ULift.up_down]
  exact hp

end CategoryTheory.TheoremB
