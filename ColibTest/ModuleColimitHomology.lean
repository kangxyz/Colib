module

public import Colib.Algebra.Category.ModuleCat.CoproductHomology

@[expose] public section

noncomputable section
open CategoryTheory Limits
universe u v w w' t

variable (R : Type v) [Ring R]
variable (J : Type w) [Category.{w'} J] [IsFiltered J]
  [UnivLE.{w, u}] [UnivLE.{w', u}]
variable {α : Type t} (c : ComplexShape α) (n : α)

example : AB5 (ModuleCat.{u} R) := ModuleCat.ab5 R

example : PreservesColimitsOfShape J
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c n) :=
  ModuleCat.homologyFunctor_preservesFilteredColimits R J c n

example (F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c) :
    (ModuleCat.filteredColimitHomologyIso R J c n F).inv =
      colimit.post F (HomologicalComplex.homologyFunctor _ c n) := rfl

example (F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c) (j : J) :
    colimit.ι (F ⋙ HomologicalComplex.homologyFunctor _ c n) j ≫
      (ModuleCat.filteredColimitHomologyIso R J c n F).inv =
        HomologicalComplex.homologyMap (colimit.ι F j) n :=
  ModuleCat.filteredColimitHomologyIso_ι_inv R J c n F j

example : AB5 (ModuleCat.{u} ℤ) := ModuleCat.ab5 ℤ

variable (ι : Type u)

example (K : ι → HomologicalComplex (ModuleCat.{u} R) c) :
    (ModuleCat.coproductHomologyIso R ι c n K).inv =
      sigmaComparison (HomologicalComplex.homologyFunctor _ c n) K := rfl

example (K : ι → HomologicalComplex (ModuleCat.{u} R) c) (i : ι) :
    Sigma.ι (fun j ↦ (K j).homology n) i ≫
      (ModuleCat.coproductHomologyIso R ι c n K).inv =
        HomologicalComplex.homologyMap (Sigma.ι K i) n :=
  ModuleCat.coproductHomologyIso_ι_inv R ι c n K i

example {K L : ι → HomologicalComplex (ModuleCat.{u} R) c}
    (f : ∀ i, K i ⟶ L i) [∀ i, QuasiIso (f i)] : QuasiIso (Limits.Sigma.map f) :=
  ModuleCat.quasiIso_sigma_map R ι c f
