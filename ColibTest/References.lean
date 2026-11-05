/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless (Colib.Library.bindings env).any (fun binding =>
      binding.id == "COL-0004" &&
      binding.declName == ``CategoryTheory.GrothendieckGroup.fgModuleRankEquiv) do
    throwError "The field computation is missing its permanent Library binding"
  unless (Colib.Library.citations env).any (fun citation =>
      citation.source == "Milnor1970" && citation.locator.startsWith "Section 1") do
    throwError "The Milnor paper reference was not retained in the compiled environment"
  let helper := ``CategoryTheory.GrothendieckGroup.fgModuleRank_of
  if (Colib.Library.bindings env).any (fun binding => binding.declName == helper) then
    throwError "The cited helper should use its ordinary Lean name"
  unless (Colib.Library.citations env).any (fun citation => citation.declName == helper) do
    throwError "A literature citation must be retained without a permanent item tag"

/-- error: Expected a permanent COL identifier with at least four digits -/
#guard_msgs in
attribute [colib_tag "invalid"] CategoryTheory.GrothendieckGroup.fgModuleRankEquiv

/-- error: Unknown literature correspondence relation unknown -/
#guard_msgs in
attribute [colib_ref "WeibelKBook" "II" "unknown" "test scope"]
  CategoryTheory.GrothendieckGroup.fgModuleRankEquiv
