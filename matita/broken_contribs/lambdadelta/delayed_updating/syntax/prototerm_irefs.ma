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
include "delayed_updating/syntax/path_proper.ma".
include "delayed_updating/notation/functions/subset_i_1.ma".

(* SUBSET OF INNER REFERENCES ***********************************************)

(* Note: we identify inner references with paths to them *)
definition pir (t): 𝒫❨ℙ❩ ≝
           {r | ∃∃p,q,k. p◖𝗱k = r & q ϵ 𝐏 & p◖𝗱k●q ϵ t}
.

interpretation
  "pointer to inner reference"
  'SubsetI t = (pir t).

(* Basic constructions ******************************************************)

lemma pir_mk (t) (p) (q) (k):
      q ϵ 𝐏 → p◖𝗱k●q ϵ t → p◖𝗱k ϵ 𝐈❨t❩.
/2 width=6 by ex3_3_intro/
qed.
