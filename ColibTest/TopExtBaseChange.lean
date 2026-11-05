module

import Colib.RingTheory.Koszul.TopExtBaseChange

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u w z

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)]
  (T : Submonoid R) [IsLocalization T A] (N : ModuleCat.{u} R)

example (f : Fin 0 → R) (hf : Koszul.IsKoszulRegular f) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    IsLocalizedModule T
      ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N 0) :=
  Koszul.seqTopExtScalarExtension_isLocalizedModule T f hf N

example (f : Fin 2 → R) (hf : Koszul.IsKoszulRegular f) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    IsLocalizedModule T
      ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N 2) :=
  Koszul.seqTopExtScalarExtension_isLocalizedModule T f hf N
