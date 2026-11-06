/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Colib.KTheory.Quillen.Resolution.Theorem
public import Colib.KTheory.Quillen.Devissage.Theorem

/-! The two structural theorems coexist after extracting the shared faithful
Q-functor lemma. Resolution retains its own extension-closed exact structure;
dévissage retains the native intrinsic abelian exact structure. -/

#check CategoryTheory.ExactCategory.Resolution.inclusionKMap_bijective
#check CategoryTheory.Abelian.Devissage.KMap_bijective
