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

include "ground/xoa/ex_3_3.ma".
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/syntax/path_proper.ma".
include "delayed_updating/notation/functions/subset_i_1.ma".

(* SUBSET OF INNER REFERENCES ***********************************************)

(* Note: we identify inner references with cleared paths to them *)
(* Note: thus we can compare these paths in computation steps *)
definition pirc (t): 𝒫❨ℙ❩ ≝
           {r | ∃∃p,q,k. (⓪p)◖𝗱𝟎 = r & q ϵ 𝐏 & p◖𝗱k●q ϵ t}
.

interpretation
  "pointer to inner reference"
  'SubsetI t = (pirc t).

(* Basic constructions ******************************************************)

lemma path_in_pirc (t) (p) (q) (k):
      q ϵ 𝐏 → p◖𝗱k●q ϵ t → ⓪p◖𝗱𝟎 ϵ 𝐈❨t❩.
/2 width=6 by ex3_3_intro/
qed.
