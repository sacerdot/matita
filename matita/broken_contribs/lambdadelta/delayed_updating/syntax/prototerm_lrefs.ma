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

include "ground/xoa/ex_2_3.ma".
include "ground/subsets/subset.ma".
include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/subset_l_1.ma".

(* SUBSET OF LOCAL REFERENCES ***********************************************)

(* Note: we identify local references with paths to them *)
definition plr (t): 𝒫❨ℙ❩ ≝
           {r | ∃∃p,q,k. p◖𝗱k = r & p◖𝗱k●q ϵ t}
.

interpretation
  "pointer to local reference"
  'SubsetL t = (plr t).

(* Basic constructions ******************************************************)

lemma plr_mk (t) (p) (q) (k):
      p◖𝗱k●q ϵ t → p◖𝗱k ϵ 𝐋❨t❩.
/2 width=5 by ex2_3_intro/
qed.
