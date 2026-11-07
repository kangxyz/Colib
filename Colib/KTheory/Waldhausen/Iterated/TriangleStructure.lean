/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.NaturalTriangle
public import Colib.KTheory.Waldhausen.Iterated.StructureHomotopy

/-!
# Independent structure-coordinate compatibility of iterated triangles

Both original insertion squares imply that the entire Δ[2] family commutes with the original
simplicial suspension coordinate Δ[1]. This is a simplicial identity; realization interchange and
a coherent two-parameter prespectrum comparison are separate steps.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/TriangleStructure.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, simplex faces,
whole fixed-zero family, and independent structure parameters are retained under native ownership.
  -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

lemma stageTriangleFunction_congr (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {F G H F' G' H' : V ⟶ W} (eF : F = F') (eG : G = G') (eH : H = H')
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (η' : F'.hom.toFunctor ⟶ G'.hom.toFunctor) (θ' : G'.hom.toFunctor ⟶ H'.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq (η'.app A)) (hθ' : ∀ A, W.obj.waldhausen.weq (θ'.app A))
    (h₁ : η ≫ eqToHom (congrArg (fun f ↦ f.hom.toFunctor) eG) =
      eqToHom (congrArg (fun f ↦ f.hom.toFunctor) eF) ≫ η')
    (h₂ : θ ≫ eqToHom (congrArg (fun f ↦ f.hom.toFunctor) eH) =
      eqToHom (congrArg (fun f ↦ f.hom.toFunctor) eG) ≫ θ')
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (σ : (Δ[2]).obj n) :
    stageTriangleFunction r η θ hη hθ n A σ =
      stageTriangleFunction r η' θ' hη' hθ' n A σ := by
  cases eF
  cases eG
  cases eH
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h₁ h₂
  subst η'
  subst θ'
  rfl

/-- The full original triangle commutes with an independent original suspension parameter. -/
theorem stageTriangleFunction_structure (r : ℕ) {V W : WideSubcategory preservesZero.{u}} {F G H : V
  ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n)
    (τ : (Δ[1]).obj n) (σ : (Δ[2]).obj n) :
    stageTriangleFunction (r + 1) η θ hη hθ n ((stageCylinder r V).app n (A, τ)) σ =
      (stageCylinder r W).app n (stageTriangleFunction r η θ hη hθ n A σ, τ) := by
  change stageTriangleFunction r (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
    (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop) n
    (((stages r).map ((insertion τ.down).app V)).app n A) σ =
      ((stages r).map ((insertion τ.down).app W)).app n
        (stageTriangleFunction r η θ hη hθ n A σ)
  rw [← stageTriangleFunction_precomp, ← stageTriangleFunction_postcomp]
  exact (stageTriangleFunction_congr r ((insertion τ.down).naturality F)
    ((insertion τ.down).naturality G) ((insertion τ.down).naturality H) _ _ _ _ _ _ _ _
    (rowsTransformation_insertion_square η τ.down)
    (rowsTransformation_insertion_square θ τ.down) n A σ).symm

end CategoryTheory.Waldhausen.IteratedS
