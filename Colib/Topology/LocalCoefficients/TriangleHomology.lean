/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.TriangleChains
public import Colib.Topology.LocalCoefficients.HomotopyInvariance

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TriangleHomology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual coefficient maps.

 # Original local homology maps of commuting spatial triangles -/

@[expose] public section
noncomputable section
open CategoryTheory Limits
open scoped Simplicial
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z W : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W]

/-- The actual triangle map retains both equality transport and pullback composition. -/
def triangleHomologyMap (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, Z))
    (w : s = t.comp h) (A : System.{u, u} Z) (n : ℕ) :
    homology (pullback s A) n ⟶ homology (pullback t A) n :=
  coefficientHomologyMap (eqToHom (congrArg (fun f ↦ pullback f A) w)) n ≫
    coefficientHomologyMap (pullbackCompositionIso h t A).hom n ≫
      pushforwardHomologyMap h (pullback t A) n

/-- The triangle homology map comes from the already constructed genuine simplicial map. -/
theorem triangleHomologyMap_eq (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, Z))
    (w : s = t.comp h) (A : System.{u, u} Z) (n : ℕ) :
    triangleHomologyMap h s t w A n =
      (HomologicalComplex.homologyFunctor _ _ n).map
        ((AlgebraicTopology.alternatingFaceMapComplex _).map
          (triangleSimplicialMap h s t w A)) := by
  simp only [triangleSimplicialMap, Functor.map_comp]
  rfl

/-- A map which is a local homology equivalence remains one with the actual triangle transport. -/
theorem triangleHomologyMap_isIso (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, Z))
    (w : s = t.comp h) (A : System.{u, u} Z) (n : ℕ)
    [IsIso (pushforwardHomologyMap h (pullback t A) n)] :
    IsIso (triangleHomologyMap h s t w A n) := by
  unfold triangleHomologyMap
  change IsIso ((coefficientHomologyIso (eqToIso
    (congrArg (fun f ↦ pullback f A) w)) n).hom ≫
      (coefficientHomologyIso (pullbackCompositionIso h t A) n).hom ≫ _)
  infer_instance

/-- Actual triangle maps compose, including every coefficient equality transport. -/
theorem triangleSimplicialMap_comp (h : C(X, Y)) (k : C(Y, W))
    (s : C(X, Z)) (t : C(Y, Z)) (r : C(W, Z))
    (wh : s = t.comp h) (wk : t = r.comp k)
    (wc : s = r.comp (k.comp h)) (A : System.{u, u} Z) :
    triangleSimplicialMap h s t wh A ≫ triangleSimplicialMap k t r wk A =
      triangleSimplicialMap (k.comp h) s r wc A := by
  subst s
  subst t
  apply NatTrans.ext
  funext n
  apply Sigma.hom_ext
  intro σ
  change chainInclusion _ σ ≫
    ((triangleSimplicialMap h ((r.comp k).comp h) (r.comp k) _ A).app n ≫
      (triangleSimplicialMap k (r.comp k) r _ A).app n) = _
  rw [← Category.assoc, triangleSimplicialMap_inclusion]
  simp only [eqToHom_refl, Category.id_comp]
  rw [triangleSimplicialMap_inclusion]
  simp only [eqToHom_refl, Category.id_comp]
  change chainInclusion (pullback r A) (k.comp (h.comp σ)) =
    chainInclusion (pullback ((r.comp k).comp h) A) σ ≫
      (triangleSimplicialMap (k.comp h) ((r.comp k).comp h) r wc A).app n
  rw [triangleSimplicialMap_inclusion]
  rfl

/-- Composition of the genuine homology triangle maps. -/
@[reassoc]
theorem triangleHomologyMap_comp (h : C(X, Y)) (k : C(Y, W))
    (s : C(X, Z)) (t : C(Y, Z)) (r : C(W, Z))
    (wh : s = t.comp h) (wk : t = r.comp k)
    (wc : s = r.comp (k.comp h)) (A : System.{u, u} Z) (n : ℕ) :
    triangleHomologyMap h s t wh A n ≫ triangleHomologyMap k t r wk A n =
      triangleHomologyMap (k.comp h) s r wc A n := by
  simp only [triangleHomologyMap_eq, ← Functor.map_comp]
  rw [triangleSimplicialMap_comp h k s t r wh wk wc]

/-- Postcomposition of the specified homotopy gives precisely the coefficient
conversion required for a homotopy of spatial triangles. -/
theorem triangleHomologyMap_homotopy {h k : C(X, Y)} (H : h.Homotopy k)
    (s s' : C(X, Z)) (t : C(Y, Z)) (wh : s = t.comp h) (wk : s' = t.comp k)
    (Q : s.Homotopy s') (hQ : ∀ a x, Q (a, x) = t (H (a, x)))
    (A : System.{u, u} Z) (n : ℕ) :
    triangleHomologyMap h s t wh A n =
      coefficientHomologyMap (homotopyPullbackIso Q A).hom n ≫
        triangleHomologyMap k s' t wk A n := by
  subst s
  subst s'
  have he : (pullbackCompositionIso h t A).hom ≫
      (homotopyPullbackIso H (pullback t A)).hom =
      (homotopyPullbackIso Q A).hom ≫ (pullbackCompositionIso k t A).hom := by
    apply NatTrans.ext
    funext x
    change 𝟙 _ ≫ transport (pullback t A) (H.evalAt x.as) =
      transport A (Q.evalAt x.as) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id, pullback_transport]
    congr 1
    apply Path.ext
    exact funext fun a ↦ (hQ a x.as).symm
  simp only [triangleHomologyMap, eqToHom_refl, coefficientHomologyMap_id,
    Category.id_comp]
  rw [pushforwardHomologyMap_homotopy H]
  change _ ≫ (coefficientHomologyMap (homotopyPullbackIso H (pullback t A)).hom n ≫ _) = _
  rw [← Category.assoc, ← coefficientHomologyMap_comp, he, coefficientHomologyMap_comp,
    Category.assoc]

/-- A triangle map followed by its original target leg is the original source leg. -/
@[reassoc]
theorem triangleHomologyMap_to_target (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, Z))
    (w : s = t.comp h) (A : System.{u, u} Z) (n : ℕ) :
    triangleHomologyMap h s t w A n ≫ pushforwardHomologyMap t A n =
      pushforwardHomologyMap s A n := by
  subst s
  simp only [triangleHomologyMap, eqToHom_refl, coefficientHomologyMap_id,
    Category.id_comp, Category.assoc]
  exact (pushforwardHomologyMap_comp h t A n).symm

end FundamentalGroupoid.LocalCoefficients
