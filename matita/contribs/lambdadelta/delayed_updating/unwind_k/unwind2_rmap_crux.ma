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

include "delayed_updating/unwind_k/unwind2_rmap_closed.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Crucial constructions with tr_uni ****************************************)

(* Note: crux of the commutation between unwind and balanced focused reduction *)
lemma unwind2_rmap_uni_crux (f) (p) (b) (q) (m) (n):
      b Ïµ ðâ¨â»,m,ðâ© â q Ïµ ðâ¨â»,n,ðâ© â
      (ð®â¨â(â­b+â­q)â© â â¶[f]p â â¶[f](pâðâbâðâq) â ð®â¨â(m+n)â©).
#f #p #b #q #m #n #Hm #Hn
<list_append_rcons_sn <list_append_rcons_sn >list_append_assoc
>list_append_rcons_sn >(list_append_rcons_sn â¦ b)
@(stream_eq_trans â¦ (tr_compose_uni_dx_pap â¦)) <tr_pap_succ_nap
@(stream_eq_trans ????? (tr_compose_eq_repl â¦))
[| @tls_succ_plus_unwind2_rmap_append_closed_Lq_dx // | skip
|  <nap_plus_unwind2_rmap_append_closed_Lq_dx // | skip
] -Hn
@tr_eq_inv_nap_zero_tl_bi
[ <tr_compose_nap <tr_compose_nap <tr_uni_nap <tr_uni_nap
  >nsucc_unfold >nplus_succ_dx >nplus_succ_dx <nplus_assoc <nplus_assoc
  >tr_nap_plus_dx <unwind2_rmap_append <nap_plus_unwind2_rmap_closed
  /2 width=4 by pcc_A_sn/
| @(stream_eq_canc_sn â¦ (tr_tl_compose_uni_sn â¦))
  @(stream_eq_trans ????? (tr_tl_compose_uni_sn â¦))
  >stream_tls_succ <unwind2_rmap_append
  /3 width=2 by tls_succ_unwind2_rmap_closed, pcc_A_sn/
]
qed-.
