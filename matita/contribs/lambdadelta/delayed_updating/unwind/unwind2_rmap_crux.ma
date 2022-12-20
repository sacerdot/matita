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

include "delayed_updating/unwind/unwind2_rmap_closed.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Crucial constructions with tr_uni ****************************************)

(* Note: crux of the commutation between unwind and balanced focused reduction *)
lemma unwind2_rmap_uni_crux (f) (p) (b) (q) (m) (n):
      b ϵ 𝐂❨Ⓕ,m,𝟎❩ → q ϵ 𝐂❨Ⓕ,n,𝟎❩ →
      (𝐮❨↑(♭b+♭q)❩ ∘ ▶[f]p ≗ ▶[f](p●𝗔◗b●𝗟◗q) ∘ 𝐮❨↑(m+n)❩).
#f #p #b #q #m #n #Hm #Hn
<list_append_rcons_sn <list_append_rcons_sn >list_append_assoc
>list_append_rcons_sn >(list_append_rcons_sn … b)
@(stream_eq_trans … (tr_compose_uni_dx_pap …)) <tr_pap_succ_nap
@(stream_eq_trans ????? (tr_compose_eq_repl …))
[| @tls_succ_plus_unwind2_rmap_append_closed_Lq_dx // | skip
|  <nap_plus_unwind2_rmap_append_closed_Lq_dx // | skip
] -Hn
@tr_eq_inv_nap_zero_tl_bi
[ <tr_compose_nap <tr_compose_nap <tr_uni_nap <tr_uni_nap
  >nsucc_unfold >nplus_succ_dx >nplus_succ_dx <nplus_assoc <nplus_assoc
  >tr_nap_plus_dx <unwind2_rmap_append <nap_plus_unwind2_rmap_closed
  /2 width=4 by pcc_A_sn/
| @(stream_eq_canc_sn … (tr_tl_compose_uni_sn …))
  @(stream_eq_trans ????? (tr_tl_compose_uni_sn …))
  >stream_tls_succ <unwind2_rmap_append
  /3 width=2 by tls_succ_unwind2_rmap_closed, pcc_A_sn/
]
qed-.
