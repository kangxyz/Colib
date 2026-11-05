/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Cycles.FiniteAlgebra

example (k A : Type*) [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    [Module.Finite k A] :
    Module.finrank k A = (Module.length A A).toNat *
      Module.finrank k (IsLocalRing.ResidueField A) :=
  IsLocalRing.finrank_eq_length_mul_residueFinrank k A
