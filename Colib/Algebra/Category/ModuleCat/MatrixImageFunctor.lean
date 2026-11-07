/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.MatrixBaseChange
public import Colib.Algebra.Category.ModuleCat.IdempotentMatrix

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/Algebra/Category/ModuleCat/MatrixImageFunctor.lean`.
The original hypotheses and maps are retained.

# Realizing formal matrix summands as actual projective right modules

The Karoubi relation ensures that its morphisms restrict to the genuine images
of the idempotents. Extending by inclusion and projection gives the inverse on
morphisms. Every finite projective right module has an idempotent presentation,
so the resulting functor is an equivalence, proved rather than assumed.
-/
@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Idempotents

namespace Matrix.RightModule

variable {R : Type u} [Ring R]

lemma linearMap_comp {P Q U : FreeCategory R} (a : P ⟶ Q) (b : Q ⟶ U) :
    linearMap (a ≫ b) = (linearMap b).comp (linearMap a) := linearMap_mul b a

/-- A compatible matrix restricts to a right-linear map between actual images. -/
def imageMap {P Q : ProjectiveMatrices R} (a : P ⟶ Q) :
    (linearMap P.p).range →ₗ[Rᵐᵒᵖ] (linearMap Q.p).range where
  toFun x := ⟨linearMap a.f x.val, by
    refine ⟨linearMap a.f x.val, ?_⟩
    have hh : (linearMap Q.p).comp (linearMap a.f) = linearMap a.f := by
      rw [← linearMap_mul]
      exact congrArg linearMap (Karoubi.comp_p a)
    exact DFunLike.congr_fun hh x.val⟩
  map_add' x y := Subtype.ext (map_add (linearMap a.f) x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (linearMap a.f) r x.val)

@[simp] lemma imageMap_apply {P Q : ProjectiveMatrices R} (a : P ⟶ Q)
    (x : (linearMap P.p).range) : (imageMap a x).val = linearMap a.f x.val := rfl

/-- Extend a map between images by the source projection and target inclusion. -/
def liftImageMap {P Q : ProjectiveMatrices R}
    (f : (linearMap P.p).range →ₗ[Rᵐᵒᵖ] (linearMap Q.p).range) : P ⟶ Q where
  f := ofLinearMap ((linearMap Q.p).range.subtype.comp
    (f.comp (linearMap P.p).rangeRestrict))
  comm := by
    apply equiv.injective
    change linearMap (_ : Matrix _ _ R) = linearMap _
    simp only [linearMap_comp, linearMap_ofLinearMap]
    apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun (rangeRestrict_comp_subtype P.p P.idem)
      ((linearMap P.p).rangeRestrict x)
    have hy := DFunLike.congr_fun (rangeRestrict_comp_subtype Q.p Q.idem)
      (f ((linearMap P.p).rangeRestrict x))
    exact (congrArg (fun y => linearMap Q.p (f y).val) hx).trans
      (congrArg Subtype.val hy)

@[simp] lemma imageMap_liftImageMap {P Q : ProjectiveMatrices R}
    (f : (linearMap P.p).range →ₗ[Rᵐᵒᵖ] (linearMap Q.p).range) :
    imageMap (liftImageMap f) = f := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change linearMap (ofLinearMap _) x.val = (f x).val
  rw [linearMap_ofLinearMap]
  exact congrArg (fun y => (f y).val)
    (DFunLike.congr_fun (rangeRestrict_comp_subtype P.p P.idem) x)

@[simp] lemma liftImageMap_imageMap {P Q : ProjectiveMatrices R} (a : P ⟶ Q) :
    liftImageMap (imageMap a) = a := by
  apply Karoubi.Hom.ext
  apply equiv.injective
  change linearMap (ofLinearMap _) = linearMap a.f
  rw [linearMap_ofLinearMap]
  have h : (linearMap a.f).comp (linearMap P.p) = linearMap a.f := by
    rw [← linearMap_mul]
    exact congrArg linearMap (Karoubi.p_comp a)
  exact h

/-- Formal summands are realized in the existing category of actual finite projective modules. -/
def imageFunctor : ProjectiveMatrices R ⥤ ModuleCat.FiniteProjective.Category.{u,u} Rᵐᵒᵖ where
  obj P := image P.p P.idem
  map a := (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).homMk (ModuleCat.ofHom (imageMap a))
  map_id P := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change linearMap P.p x.val = x.val
    exact congrArg Subtype.val (DFunLike.congr_fun (rangeRestrict_comp_subtype P.p P.idem) x)
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change linearMap (a.f ≫ b.f) x.val = linearMap b.f (linearMap a.f x.val)
    exact DFunLike.congr_fun (linearMap_mul b.f a.f) x.val

/-- Every morphism of actual images comes from exactly one compatible matrix. -/
def imageFunctorFullyFaithful : (imageFunctor (R := R)).FullyFaithful where
  preimage f := liftImageMap f.hom.hom
  map_preimage f := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact imageMap_liftImageMap f.hom.hom
  preimage_map a := liftImageMap_imageMap a

instance : (imageFunctor (R := R)).Full := imageFunctorFullyFaithful.full
instance : (imageFunctor (R := R)).Faithful := imageFunctorFullyFaithful.faithful

instance : (imageFunctor (R := R)).EssSurj where
  mem_essImage M := by
    obtain ⟨n, A, hA, ⟨e⟩⟩ := exists_idempotent_image M.obj
    exact ⟨⟨⟨n⟩, A, hA⟩, ⟨(ModuleCat.FiniteProjective.property Rᵐᵒᵖ).isoMk e.symm.toModuleIso⟩⟩

instance : (imageFunctor (R := R)).IsEquivalence where
/-- The Karoubi model is equivalent to actual finite projective right modules. -/
def imageEquivalence : ProjectiveMatrices R ≌ ModuleCat.FiniteProjective.Category.{u,u} Rᵐᵒᵖ :=
  imageFunctor.asEquivalence

end Matrix.RightModule
