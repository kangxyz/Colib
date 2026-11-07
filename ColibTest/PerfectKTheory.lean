module

import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen
import Colib.KTheory.Waldhausen.ExactEquivalence

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

variable (X : RingedSpace.{u, u})

-- Notation for the existing structure is local to these tests; no new object is defined.
local notation "W" => RingedSpace.perfectComplexesWaldhausen X

example (n : ℕ) : Waldhausen.KMap (Waldhausen.IsExact.id (W).cof (W).weq) n =
    MonoidHom.id ((W).K n) := Waldhausen.KMap_id W n

example (n : ℕ) :
    (Waldhausen.KMap (Waldhausen.IsExact.id (W).cof (W).weq) n).comp
      (Waldhausen.KMap (Waldhausen.IsExact.id (W).cof (W).weq) n) =
        Waldhausen.KMap ((Waldhausen.IsExact.id (W).cof (W).weq).comp
          (Waldhausen.IsExact.id (W).cof (W).weq)) n :=
  Waldhausen.KMap_comp_KMap (Waldhausen.IsExact.id (W).cof (W).weq)
    (Waldhausen.IsExact.id (W).cof (W).weq) n

-- The generic theorem applies directly to the native category's reflexive equivalence.
example (n : ℕ) :
    (Waldhausen.KEquivOfExactEquivalence (CategoryTheory.Equivalence.refl :
      (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X))) ≌
        (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X))))
      (Waldhausen.IsExact.id (W).cof (W).weq)
      (Waldhausen.IsExact.id (W).cof (W).weq) n).toMonoidHom =
        MonoidHom.id ((W).K n) := Waldhausen.KMap_id W n

example (n : ℕ) :
    (Waldhausen.KEquivOfExactEquivalence (CategoryTheory.Equivalence.refl :
      (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X))) ≌
        (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X))))
      (Waldhausen.IsExact.id (W).cof (W).weq)
      (Waldhausen.IsExact.id (W).cof (W).weq) n).symm.toMonoidHom =
        MonoidHom.id ((W).K n) := Waldhausen.KMap_id W n

example (n : ℕ) :
    Waldhausen.KMap (Waldhausen.IsExact.id (W).cof (W).weq) n =
      HomotopyGroup.piMap n (Waldhausen.deloopingMap
        (Waldhausen.IsExact.id (W).cof (W).weq)).hom
        (Waldhausen.deloopingMap_basepoint_of_zeroEq
          (Waldhausen.IsExact.id (W).cof (W).weq) rfl) :=
  Waldhausen.KMap_eq_piMap_of_zeroEq (Waldhausen.IsExact.id (W).cof (W).weq) rfl n

-- The actual natural-transformation cylinder fixes the native chosen basepoint.
example :
    (Waldhausen.deloopingMap (Waldhausen.IsExact.id (W).cof (W).weq)).hom.HomotopyRel
      (Waldhausen.deloopingMap (Waldhausen.IsExact.id (W).cof (W).weq)).hom {(W).kBasepoint} :=
  Waldhausen.weakNaturalTransformationBasedHomotopy W W
    (Waldhausen.IsExact.id (W).cof (W).weq) (Waldhausen.IsExact.id (W).cof (W).weq)
    (𝟙 _) (fun _ => (W).weq_iso _ inferInstance) rfl rfl
