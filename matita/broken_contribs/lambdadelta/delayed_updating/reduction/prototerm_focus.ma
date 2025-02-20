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

include "ground/subsets/subset_and.ma".
include "delayed_updating/reduction/prototerm_xfocus.ma".
include "delayed_updating/notation/functions/subset_f_4.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

definition brf (t) (p) (b) (q): 𝒫❨ℙ❩ ≝
           t ∩ 𝐅❨p,b,q❩
.

interpretation
  "balanced reduction focus (subset of paths)"
  'SubsetF t p b q = (brf t p b q).

(* Basic constructions ******************************************************)

lemma brf_unfold (t) (p) (b) (q):
      t ∩ 𝐅❨p,b,q❩ = 𝐅❨t,p,b,q❩.
//
qed.
