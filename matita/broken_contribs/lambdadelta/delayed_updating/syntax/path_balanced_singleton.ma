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

include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/syntax/path_singleton.ma".
include "ground/lib/subset.ma".

(* BALANCE CONDITION FOR PATH ***********************************************)

(* Constructionswith singleton for path *************************************)

lemma pbc_ALs (n) (b):
      b ϵ 𝐁 → (𝗔∗∗n)●b● 𝗟∗∗n ϵ 𝐁.
#n @(nat_ind_succ … n) -n [| #n #IH ] #b #Hb
[ <list_singleton_zero //
| <list_singleton_succ_rcons <list_singleton_succ_lcons
  >list_append_rcons_sn <list_append_rcons_sn in ⊢ (%%%(%%%?));
  /3 width=1 by pbc_redex/
]
qed.
