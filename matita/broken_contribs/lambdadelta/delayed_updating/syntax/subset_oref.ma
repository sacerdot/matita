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

include "ground/subsets/subset.ma".
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/notation/functions/subset_or_1.ma".

(* SUBSET OF OUTER REFERENCES ***********************************************)

(* Note: we identify outer references with cleared paths to them *)
(* Note: thus we can compare these paths in computation steps *)
definition porc (t): 𝒫❨ℙ❩ ≝
           {r | ∃∃p,n. ⓪(p◖𝗱n) = r & p◖𝗱n ϵ t}
.

interpretation
  "pointer to outer reference (path subset)"
  'SubsetOR t = (porc t).

(* Basic constructions ******************************************************)

lemma porc_mk (t) (p) (n):
      p◖𝗱n ϵ t → ⓪(p◖𝗱n) ϵ 𝐎𝐑❨t❩.
/2 width=4 by ex2_2_intro/
qed.
