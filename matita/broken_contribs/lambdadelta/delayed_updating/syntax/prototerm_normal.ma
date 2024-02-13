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

include "ground/lib/subset_le.ma".
include "ground/lib/subset_empty.ma".
include "ground/lib/subset_singleton.ma".
include "delayed_updating/notation/functions/subset_nf_0.ma".
include "delayed_updating/syntax/path_reducible.ma".

(* NORMAL FORM FOR PROTOTERM ************************************************)

definition tnf: 𝒫❨𝕋❩ ≝
           {t | 𝐑❨t❩ ⊆ Ⓕ}
.

interpretation
  "normal form (prototerm)"
  'SubsetNF = (tnf).

(* Basic inversion **********************************************************)

lemma tnf_inv_gen (t) (r):
      t ϵ 𝐍𝐅 → r ϵ 𝐑❨t❩ → ⊥.
/2 width=3 by/
qed-.

(* Basic constructions ******************************************************)

lemma tnf_empty: Ⓕ ϵ 𝐍𝐅.
#r * #p #b #q #n #_ #_ #_ #Hn elim Hn
qed.

lemma tnf_null: ❴𝐞❵ ϵ 𝐍𝐅.
#r * #p #b #q #n #_ #_ #_ #Hn destruct
qed.

lemma tnf_lcons (t) (l):
      (𝗔 ⧸= l) → t ϵ 𝐍𝐅 → l◗t ϵ 𝐍𝐅.
#t #l #Hl #Ht #r * #p
@(list_ind_rcons … p) -p
[ #b #q #n #_ #_ #_
  <list_append_empty_dx >list_append_lcons_sn #Hn
  elim (append_in_comp_inv_lcons_bi … Hn) -Hn #H0 #_
  elim Hl -Hl //
| #p #l0 #_ #b #q #n #Hr #Hb #Hq
  <list_append_rcons_dx >list_append_lcons_sn #Hn
  elim (append_in_comp_inv_lcons_bi … Hn) -Hn #H0 #Hn destruct
  elim (tnf_inv_gen … (⓪(p●𝗔◗b●𝗟◗q)) Ht) -Ht -l
  /2 width=3 by prc_mk/
]
qed.
