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
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/notation/functions/subset_l_1.ma".

(* SUBSET OF LOCAL REFERENCES ***********************************************)

(* Note: we identify local references with cleared paths to them *)
(* Note: thus we can compare these paths in computation steps *)
definition plrc (t): 𝒫❨ℙ❩ ≝
           {r | ∃∃p,q,k. ⓪p◖𝗱𝟎 = r & p◖𝗱k●q ϵ t}
.

interpretation
  "pointer to local reference"
  'SubsetL t = (plrc t).

(* Basic constructions ******************************************************)

lemma path_in_plrc (t) (p) (q) (k):
      p◖𝗱k●q ϵ t → ⓪p◖𝗱𝟎 ϵ 𝐋❨t❩.
/2 width=5 by ex2_3_intro/
qed.
