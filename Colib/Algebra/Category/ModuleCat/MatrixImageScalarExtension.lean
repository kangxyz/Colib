/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.MatrixImageFunctor
public import Colib.LinearAlgebra.Matrix.RightScalarExtension

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/Algebra/Category/ModuleCat/MatrixImageScalarExtension.lean`.
The original hypotheses and maps are retained.

# Scalar extension of genuine idempotent images

The actual inclusion and idempotent retraction transport the finite-free universal
property to the original matrix images. The target is any right module, in an
independent universe; it is not assumed finite or projective.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w w'
namespace Matrix.RightModule
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)

/-- Entrywise change of rings sends the actual idempotent image into its mapped image. -/
def imageUnit (P : ProjectiveMatrices R) :
    (linearMap P.p).range →ₛₗ[f.op] (linearMap (P.p.map f)).range where
  toFun x := ⟨coordinateBaseChange f x.val, by
    obtain ⟨y, hy⟩ := x.property
    refine ⟨coordinateBaseChange f y, ?_⟩
    rw [← coordinateBaseChange_linearMap, hy]⟩
  map_add' x y := Subtype.ext (map_add (coordinateBaseChange f) x.val y.val)
  map_smul' r x := Subtype.ext ((coordinateBaseChange f).map_smulₛₗ r x.val)

/-- The original unit is literally entrywise application of the ring homomorphism. -/
theorem imageUnit_apply (P : ProjectiveMatrices R) (x : (linearMap P.p).range)
    (i : Fin P.X.rank) : (imageUnit f P x).val i = f (x.val i) := rfl

/-- The unit commutes with the actual idempotent retractions. -/
theorem imageUnit_rangeRestrict (P : ProjectiveMatrices R) (x : Fin P.X.rank → R) :
    imageUnit f P ((linearMap P.p).rangeRestrict x) =
      (linearMap (P.p.map f)).rangeRestrict (coordinateBaseChange f x) := by
  apply Subtype.ext
  exact coordinateBaseChange_linearMap f P.p x

variable (P : ProjectiveMatrices R) (N : Type w) [AddCommGroup N] [Module Sᵐᵒᵖ N]

/-- Extend through the original idempotent retraction, then restrict along the actual inclusion. -/
def imageExtensionLift (h : (linearMap P.p).range →ₛₗ[f.op] N) :
    (linearMap (P.p.map f)).range →ₗ[Sᵐᵒᵖ] N :=
  ((freeScalarExtensionEquiv f).symm
    (h.comp (linearMap P.p).rangeRestrict)).comp (linearMap (P.p.map f)).range.subtype

/-- The extension restricts to the original semilinear map on the actual image. -/
theorem imageExtensionLift_unit (h : (linearMap P.p).range →ₛₗ[f.op] N)
    (x : (linearMap P.p).range) :
    imageExtensionLift f P N h (imageUnit f P x) = h x := by
  have he := DFunLike.congr_fun
    ((freeScalarExtensionEquiv f).apply_symm_apply
      (h.comp (linearMap P.p).rangeRestrict)) x.val
  change imageExtensionLift f P N h (imageUnit f P x) =
    h ((linearMap P.p).rangeRestrict x.val) at he
  exact he.trans (congrArg h
    (DFunLike.congr_fun (rangeRestrict_comp_subtype P.p P.idem) x))

/-- A linear map on the mapped image is recovered from its restriction along the unit. -/
theorem imageExtensionLift_restrict (k : (linearMap (P.p.map f)).range →ₗ[Sᵐᵒᵖ] N) :
    imageExtensionLift f P N (k.comp (imageUnit f P)) = k := by
  have he : (freeScalarExtensionEquiv f).symm
      ((k.comp (imageUnit f P)).comp (linearMap P.p).rangeRestrict) =
      k.comp (linearMap (P.p.map f)).rangeRestrict := by
    apply (freeScalarExtensionEquiv f).injective
    rw [AddEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro x
    exact congrArg k (imageUnit_rangeRestrict f P x)
  apply LinearMap.ext
  intro x
  change ((freeScalarExtensionEquiv f).symm
    ((k.comp (imageUnit f P)).comp (linearMap P.p).rangeRestrict)) x.val = k x
  rw [he]
  exact congrArg k (DFunLike.congr_fun
    (rangeRestrict_comp_subtype ((baseChange f).obj P).p ((baseChange f).obj P).idem) x)

/-- The actual mapped image represents semilinear maps from the original image. -/
def imageExtensionHomEquiv :
    ((linearMap (P.p.map f)).range →ₗ[Sᵐᵒᵖ] N) ≃+
      ((linearMap P.p).range →ₛₗ[f.op] N) where
  toFun k := k.comp (imageUnit f P)
  invFun h := imageExtensionLift f P N h
  left_inv k := imageExtensionLift_restrict f P N k
  right_inv h := by
    apply LinearMap.ext
    intro x
    exact imageExtensionLift_unit f P N h x
  map_add' k l := by
    apply LinearMap.ext
    intro x
    rfl

/-- The universal equivalence is literally precomposition by the original unit. -/
theorem imageExtensionHomEquiv_apply
    (k : (linearMap (P.p.map f)).range →ₗ[Sᵐᵒᵖ] N) :
    imageExtensionHomEquiv f P N k = k.comp (imageUnit f P) := rfl

/-- The representing equivalence is natural in every target right module. -/
theorem imageExtensionHomEquiv_postcomp {N' : Type w'} [AddCommGroup N'] [Module Sᵐᵒᵖ N']
    (g : N →ₗ[Sᵐᵒᵖ] N') (k : (linearMap (P.p.map f)).range →ₗ[Sᵐᵒᵖ] N) :
    imageExtensionHomEquiv f P N' (g.comp k) =
      g.comp (imageExtensionHomEquiv f P N k) := rfl

/-- The original image unit commutes with every compatible rectangular matrix. -/
theorem imageUnit_naturality {P Q : ProjectiveMatrices R} (a : P ⟶ Q)
    (x : (linearMap P.p).range) :
    imageUnit f Q (imageMap a x) = imageMap ((baseChange f).map a) (imageUnit f P x) := by
  apply Subtype.ext
  exact coordinateBaseChange_linearMap f a.f x.val

/-- The same rectangular compatibility as equality of the actual semilinear maps. -/
theorem imageUnit_naturality_comp {P Q : ProjectiveMatrices R} (a : P ⟶ Q) :
    (imageMap ((baseChange f).map a)).comp (imageUnit f P) =
      (imageUnit f Q).comp (imageMap a) := by
  apply LinearMap.ext
  intro x
  exact (imageUnit_naturality f a x).symm

/-- The universal equivalence retains the original compatible rectangular source maps. -/
theorem imageExtensionHomEquiv_precomp {Q : ProjectiveMatrices R} (a : P ⟶ Q)
    (k : (linearMap (Q.p.map f)).range →ₗ[Sᵐᵒᵖ] N) :
    imageExtensionHomEquiv f P N (k.comp (imageMap ((baseChange f).map a))) =
      (imageExtensionHomEquiv f Q N k).comp (imageMap a) := by
  apply LinearMap.ext
  intro x
  exact (congrArg k (imageUnit_naturality f a x)).symm

end Matrix.RightModule
