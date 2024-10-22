(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/notation/functions/atsharp_2.ma".
include "explicit_updating/syntax/term.ma".
include "explicit_updating/notation/functions/category_s_0.ma".

(* SUBSTITUTION *************************************************************)

definition substitution: Type[0] ≝ ℕ⁺ → 𝕋.

interpretation
  "substitution (term)"
  'CategoryS = (substitution).

definition subst_dapp (S:𝕊): 𝕊 ≝ S.

interpretation
  "depth application (substitution)"
  'AtSharp S p = (subst_dapp S p).
