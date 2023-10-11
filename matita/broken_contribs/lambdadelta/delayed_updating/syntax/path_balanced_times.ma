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

include "delayed_updating/syntax/label_times.ma".
include "delayed_updating/syntax/path_balanced.ma".

(* BALANCE CONDITION FOR PATH ***********************************************)

(* Constructions with product for labels ************************************)

lemma pbc_redexes (n) (b):
      b ϵ 𝐁 → (𝗔*n)●b●(𝗟*n) ϵ 𝐁.
#n @(nat_ind_succ … n) -n [| #n #IH ] #b #Hb
[ <list_times_zero //
| <list_times_succ_rcons <list_times_succ_lcons
  >path_append_lcons_append <path_append_append_lcons
  /3 width=1 by pbc_redex/
]
qed.
