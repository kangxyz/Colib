import Colib.Topology.Realization.GraphAttachmentFullness

noncomputable section

open CategoryTheory CategoryTheory.Limits Convexity Convexity.StdSimplex
open scoped unitInterval
universe u v w

#check TopCat.GraphAttachment.pathImage
#check TopCat.GraphAttachment.pathImage_eq_top
#check TopCat.GraphAttachment.path_from_original_edges
#check TopCat.GraphAttachment.map_surjective_of_ambient_full

namespace TopCat.GraphAttachment

variable (X : TopCat.{u}) [DiscreteTopology X] {V D Y : TopCat.{u}}
    [DiscreteTopology V]
    {f : TopCat.of (X × simplexBoundary 1) ⟶ V}
    {g : TopCat.of (X × StdSimplex ℝ (Fin 2)) ⟶ D} {j : V ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion X 1) f g j)
    (h : C(D, Y)) {A : Type v} [Groupoid.{w} A]
    (F : A ⥤ FundamentalGroupoid Y) (vertex : V → A)
    (ε : ∀ c : V, F.obj (vertex c) ≅ FundamentalGroupoid.mk (h (j c)))
    (edge : ∀ a : X, vertex (f (a, boundaryZero)) ⟶ vertex (f (a, boundaryOne)))
    (hedge : ∀ a : X, spoke X sq h F vertex ε a (StdSimplex.single 1) =
      F.map (edge a) ≫ (vertexIso X sq h F vertex ε a boundaryOne).hom)


omit [DiscreteTopology X] [DiscreteTopology V] in
example (anchor : ∀ z : D, Anchor X sq h F vertex ε z) :
    Subgroupoid (FundamentalGroupoid D) := pathImage X sq h F vertex ε anchor

example {c d : V} (p : Path (j c) (j d)) :
    ∃ q : vertex c ⟶ vertex d,
      F.map q = (ε c).hom ≫
        (⟦p.map h.continuous⟧ : FundamentalGroupoid.mk (h (j c)) ⟶
          FundamentalGroupoid.mk (h (j d))) ≫ (ε d).inv :=
  path_from_original_edges X sq h F vertex ε edge hedge p

example [(FundamentalGroupoid.map h).Full] (c d : V) :
    Function.Surjective (F.map : (vertex c ⟶ vertex d) →
      (F.obj (vertex c) ⟶ F.obj (vertex d))) :=
  map_surjective_of_ambient_full X sq h F vertex ε edge hedge c d

end TopCat.GraphAttachment
