/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.FreeAlgebra.Map

universe u v w

variable {R : Type u} [CommSemiring R] {X : Type v} {Y : Type w}

example [Nonempty X] (f : X → Y) (hf : Function.Injective f)
    (a b : FreeAlgebra R X)
    (h : FreeAlgebra.lift R (FreeAlgebra.ι R ∘ f) a =
      FreeAlgebra.lift R (FreeAlgebra.ι R ∘ f) b) : a = b :=
  FreeAlgebra.lift_ι_injective f hf h

example (f : X → Y) (g : Y → X) :
    (FreeAlgebra.lift R (FreeAlgebra.ι R ∘ g)).comp
        (FreeAlgebra.lift R (FreeAlgebra.ι R ∘ f)) =
      FreeAlgebra.lift R (FreeAlgebra.ι R ∘ (g ∘ f)) :=
  FreeAlgebra.lift_ι_comp_lift_ι f g
