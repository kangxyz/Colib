/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

import Colib
meta import Batteries.Tactic.Lint

/-!
# Partial simplex straightening simplification regression

The full production import is intentional: constructor injectivity must simplify
in the presence of all production instances and simplification rules.
-/

open Lean Elab Command in
run_cmd do
  let isSimp ← liftCoreM <|
    (Batteries.Tactic.Lint.isSimpTheorem
      ``stdSimplex.PartialSimplexStraightening.mk.injEq).run' mkMetaContext
  unless isSimp do
    throwError "The constructor injectivity theorem is absent from the simp set"
  let failure? ← liftCoreM <| Core.withCurrHeartbeats <|
    (Batteries.Tactic.Lint.simpNF.test
      ``stdSimplex.PartialSimplexStraightening.mk.injEq).run' mkMetaContext
  if let some failure := failure? then
    throwError "{failure}"
