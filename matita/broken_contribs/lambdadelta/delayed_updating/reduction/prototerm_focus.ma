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

include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/notation/functions/subset_f_3.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

definition brf (p) (b) (q): 𝒫❨ℙ❩ ≝
           ↑(p●𝗔◗b●𝗟◗q)
.

interpretation
  "balanced reduction focus (subset of paths)"
  'SubsetF p b q = (brf p b q).

(* Basic constructions ******************************************************)

lemma brf_unfold (p) (b) (q):
      ↑(p●𝗔◗b●𝗟◗q) = 𝐅❨p,b,q❩.
//
qed.
