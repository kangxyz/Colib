module

import Colib.RingTheory.Koszul.TopExtBaseChangeQuotient

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u w z

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)]

example (I : Ideal R) (a : A) (r : R) :
    (ModuleCat.extendScalarsQuotientIso (A := A) I).hom
      (a ⊗ₜ[R] (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap R A r * a) :=
  ModuleCat.extendScalarsQuotientIso_hom_tmul I a r

example (T : Submonoid R) [IsLocalization T A]
    (f : Fin 0 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    IsLocalizedModule T
      ((Koszul.scalarExtensionQuotientExtEquiv (A := A) (Ideal.span (Set.range f)) N 0).toLinearMap.comp
        ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
          (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N 0)) :=
  Koszul.seqTopExtScalarExtensionQuotient_isLocalizedModule T f hf N

example (T : Submonoid R) [IsLocalization T A]
    (f : Fin 2 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    IsLocalizedModule T
      ((Koszul.scalarExtensionQuotientExtEquiv (A := A) (Ideal.span (Set.range f)) N 2).toLinearMap.comp
        ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
          (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N 2)) :=
  Koszul.seqTopExtScalarExtensionQuotient_isLocalizedModule T f hf N
