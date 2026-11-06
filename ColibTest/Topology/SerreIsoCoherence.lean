module
public import Colib.CategoryTheory.TheoremB.StructuredIsoHomotopy
public import Colib.CategoryTheory.TheoremB.StructuredFunctorIso
@[expose] public section
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G : C ⥤ D}

-- Exact path coordinates, not merely equality of homotopy classes.
example (α : F ⟶ G) (c : C) (t : unitInterval) :
    classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpacePoint c) =
      classifyingSpacePath (α.app c) t :=
  classifyingSpaceNaturalTransformationHomotopy_vertex α c t

example (e : F ≅ G) (x : ClassifyingSpace C) (t : unitInterval) :
    naturalIsoInverseHomotopy e (0, (t, x)) =
      classifyingSpaceNaturalTransformationHomotopy e.inv (t, x) :=
  (naturalIsoInverseHomotopy e).map_zero_left _

example (e : F ≅ G) (x : ClassifyingSpace C) (s : unitInterval) :
    naturalIsoInverseHomotopy e (s, (0, x)) = classifyingSpaceMap G x := by
  exact ((naturalIsoInverseHomotopy e).prop' s (0, x) (Or.inl rfl)).trans
    ((classifyingSpaceNaturalTransformationHomotopy e.inv).map_zero_left x)

example (e : F ≅ G) (c : C) (d : D) (hF : F.obj c = d) (hG : G.obj c = d)
    (hthin : ∀ Y : D, Subsingleton (Y ⟶ d)) (s t : unitInterval) :
    naturalIsoInverseHomotopy e (s, (t, classifyingSpacePoint c)) = classifyingSpacePoint d :=
  naturalIsoInverseHomotopy_vertex_of_subsingleton e c d hF hG hthin s t

example {A : Type u} [SmallCategory A] (P : A ⥤ C) (d : D)
    (e : P ⋙ F ≅ (Functor.const A).obj d) (s : unitInterval) (x : ClassifyingSpace A) :
    (TheoremB.naturalIsoFiberLiftHomotopy P F d e (s, x)).1.1 = classifyingSpaceMap P x := rfl

example {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(A, X)) (y : Y)
    (H K : (f.comp g).Homotopy (ContinuousMap.const A y))
    (R : H.toContinuousMap.HomotopyRel K.toContinuousMap
      (fun z : unitInterval × A ↦ z.1 = 0 ∨ z.1 = 1)) (s t : unitInterval) (x : A) :
    (HomotopyFiber.fiberLiftNullhomotopyHomotopy f g y H K R (s, x)).1.2 t =
      R (s, (t, x)) := rfl
