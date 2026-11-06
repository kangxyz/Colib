import Colib.Topology.Realization.ChainCoreNerve

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology

universe u v

variable (D : Type u) [Category.{v} D]

example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := chainCoreNerve D

example {n : ℕ} (G : ComposableArrows (Core (ComposableArrows D n)) n)
    (i : Fin (n + 1)) : (SSet.ChainCore.evaluationSimplex G).obj i = (G.obj i).of.obj i := rfl

example {n : ℕ} (G : ComposableArrows (Core (ComposableArrows D n)) n)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (SSet.ChainCore.evaluationSimplex G).map f =
      (G.map f).iso.hom.app i ≫ (G.obj j).of.map f := rfl

example : SSet.ChainCore.constant D ≫ SSet.ChainCore.evaluation D = 𝟙 (nerve D) :=
  SSet.ChainCore.constant_evaluation D

example {n : ℕ} (F : ComposableArrows D n) :
    SSet.ChainCore.evaluationSimplex ((Functor.const (Fin (n + 1))).obj (Core.mk F)) = F :=
  SSet.ChainCore.evaluationSimplex_constant F

example {p q : SimplexCategory}
    (G : ComposableArrows (Core (ComposableArrows D q.len)) q.len) (α : p ⟶ q)
    (s t : Fin (p.len + 1)) :
    SSet.ChainCore.rowTransport ((SimplexCategory.toCat.map α).toFunctor ⋙ G) s t =
      SSet.ChainCore.rowTransport G (α.toOrderHom s) (α.toOrderHom t) :=
  SSet.ChainCore.rowTransport_precomp G α s t

example {p q : SimplexCategory}
    (G : ComposableArrows (Core (ComposableArrows D q.len)) q.len) (α : p ⟶ q)
    (ψ : Fin (q.len + 1) → Fin 2) :
    SSet.ChainCore.cylinderSimplex
        ((SimplexCategory.toCat.map α).toFunctor ⋙ G ⋙ chainCoreReindex D α)
        (ψ ∘ α.toOrderHom) =
      (SimplexCategory.toCat.map α).toFunctor ⋙ SSet.ChainCore.cylinderSimplex G ψ ⋙
        chainCoreReindex D α := SSet.ChainCore.cylinderSimplex_reindex G α ψ

example : SSet.ι₀ ≫ SSet.ChainCore.cylinder D = 𝟙 (SSet.diagonalSSet (chainCoreNerve D)) :=
  SSet.ChainCore.cylinder_zero D

example : SSet.ι₁ ≫ SSet.ChainCore.cylinder D =
    SSet.ChainCore.evaluation D ≫ SSet.ChainCore.constant D := SSet.ChainCore.cylinder_one D

example : (SSet.ChainCore.realizationHomotopyEquiv D).toFun =
    (SSet.toTop.map (SSet.ChainCore.evaluation D)).hom := rfl

example : (SSet.ChainCore.realizationHomotopyEquiv D).invFun =
    (SSet.toTop.map (SSet.ChainCore.constant D)).hom := rfl

example {n : ℕ} (F : ComposableArrows D n) (ψ : Fin (n + 1) → Fin 2) :
    SSet.ChainCore.cylinderSimplex ((Functor.const (Fin (n + 1))).obj (Core.mk F)) ψ =
      (Functor.const (Fin (n + 1))).obj (Core.mk F) :=
  SSet.ChainCore.cylinderSimplex_constant F ψ

example : (SSet.ChainCore.constant D ▷ Δ[1]) ≫ SSet.ChainCore.cylinder D =
    fst (nerve D) Δ[1] ≫ SSet.ChainCore.constant D := SSet.ChainCore.constant_cylinder D

example (x : (nerve D) _⦋0⦌) (t : unitInterval) :
    SSet.realizationSimplicialHomotopy (SSet.ChainCore.homotopy D)
      (t, SSet.realizationPoint ((SSet.ChainCore.constant D).app _ x)) =
        SSet.realizationPoint ((SSet.ChainCore.constant D).app _ x) :=
  SSet.ChainCore.realizationHomotopy_fixed_vertex D x t
